-- Prove2me | Theorems.Thm_SatisficingTS_sRegret_le_tsum_discounted_gap
-- name    : SatisficingTS.sRegret_le_tsum_discounted_gap
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:24:51.551525+00:00
-- url     : https://prove2.me/theorems/c0d67184-f2a3-4c03-a57b-2c4ffa8bb392
-- title:
--   Proof of Theorem 1, p.9 — $\mathrm{SRegret}(\alpha,\psi,D)\le\sum_t\alpha^t\,\mathbb E[\tilde R-R_t]$ (corrected: the printed equality is an inequality)
-- statement:
--   Let $\alpha\in[0,1)$, let $D$ be a real number, let $\psi$ be any policy and let $\tilde A$ be any action-valued random variable whose reward $\tilde R=\mu(\tilde A,\theta)$ satisfies
--   $$
--   \mathbb E[\tilde R]\ \ge\ \mathbb E[R^*]-D .
--   $$
--   Assume $R^*$, $\tilde R$ and every $R_t$ are integrable and $\mathbb E\bigl[\sum_{t}\alpha^t|R^*-D-R_t|\bigr]<\infty$. Then the series $\sum_t\alpha^t\bigl(\mathbb E[\tilde R]-\mathbb E[R_t]\bigr)$ converges and
--   $$
--   \mathrm{SRegret}(\alpha,\psi,D)\ \le\ \sum_{t=0}^{\infty}\alpha^{t}\,\bigl(\mathbb E[\tilde R]-\mathbb E[R_t]\bigr).
--   $$
--
--   This reduces the satisficing regret to the per-period expected shortfalls relative to the benchmark, the quantities the information ratio controls.
--
--   Differences from the source:
--   - correction: SRegret(α, ψ, D) = ∑_t α^t E[R̃ − R_{t,A_t}] → ≤; reason: the equality fails when E[R̃] > E[R*] − D: one action with reward 1, θ constant, D = 1/2, Ã = that action gives SRegret = −D/(1−α) < 0 = ∑ α^t E[R̃ − R_t]; the hypothesis E[R̃] ≥ E[R*] − D gives ≤
--   - reading: R_{t,A_t} → R_t = R(Y_t); reason: the reward of the action played in period t, as defined on p.4
--   - generalization: under the hypotheses of Theorem 1 (§2 model, benchmark Ã = f(θ, ξ), D ≥ 0) → any processes θ, W, ξ, any ψ, g, any random action Ã, any real D, only α ∈ [0,1), the integrability hypotheses and E[R̃] ≥ E[R*] − D; reason: the step uses only these; the paper's setting is a special case
--   - generalization: the series ∑ α^t E[R̃ − R_t] → also asserts that the series converges; reason: extra conclusion; the paper's statement is the inequality part
--   - encoding: E[R̃ − R_t]; R* and R_t unrestricted → E[R̃] − E[R_t] with R*, R̃, R_t integrable and ∫⁻ ∑ α^t|R* − D − R_t| < ∞; reason: these make the paper's expectations and series defined; equal under integrability
-- source:
--   Russo & Van Roy, Satisficing in Time-Sensitive Bandit Learning, arXiv:1803.02855v2, proof of Theorem 1, p.9, first line of the chain (SRegret(α, ψ, D) = E[∑ αt(R∗ − D − Rt)] = ∑ αt E[R̃ − R_{t,At}])

import Mathlib
import Definitions.Def_SatisficingTS_obs
import Definitions.Def_ThompsonTutorial_InfoRatio_meanReward
import Definitions.Def_SatisficingTS_supReward
import Definitions.Def_SatisficingTS_sRegret
open MeasureTheory ThompsonTutorial.InfoRatio
open scoped ENNReal

namespace SatisficingTS

/-- **Regret reduction to the per-period shortfalls** (Russo & Van Roy, *Satisficing in
Time-Sensitive Bandit Learning*, arXiv:1803.02855v2, proof of Theorem 1, p.9, first line of the
chain: `SRegret(α, ψ, D) = E[∑_{t=0}^∞ α^t(R∗ − D − Rt)] = ∑_{t=0}^∞ α^t E[R̃ − R_{t,A_t}]`).

For a discount factor `α ∈ [0, 1)`, a level `D`, any policy `ψ` and any action-valued random
variable `Ã` with `E[µ(Ã, θ)] ≥ E[R*] − D`, if `R*`, `R̃ = µ(Ã, θ)` and every `R_t` are integrable
and `E[∑_t α^t |R* − D − R_t|] < ∞`, then the series `∑_t α^t (E[R̃] − E[R_t])` converges and
`SRegret(α, ψ, D) ≤ ∑_{t=0}^∞ α^t (E[R̃] − E[R_t])`.

**Formalization Note.** The printed first "=" is "≤" under the hypothesis `E[R̃] ≥ E[R*] − D`
(equality iff `E[R̃] = E[R*] − D`); `R_{t,A_t}` is `R_t = R(Y_t)`. -/
theorem sRegret_le_tsum_discounted_gap
    {Ω Θ 𝒲 Ξ 𝒜 𝒴 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒲]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (θ : Ω → Θ) (W : ℕ → Ω → 𝒲) (ξ : Ω → Ξ) (g : 𝒜 → Θ → 𝒲 → 𝒴) (R : 𝒴 → ℝ)
    (ψ : (t : ℕ) → (Fin t → 𝒜 × 𝒴) → Ξ → 𝒜) (Ã : Ω → 𝒜)
    (α D : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hRstar_int : Integrable (fun ω => supReward P W g R (θ ω)) P)
    (hRtilde_int : Integrable (fun ω => meanReward g R (P.map (W 0)) (Ã ω) (θ ω)) P)
    (hRt_int : ∀ t, Integrable (fun ω => R (obs ψ g θ W ξ t ω).2) P)
    (hsum : ∫⁻ ω, ∑' t, ENNReal.ofReal
        (α ^ t * |supReward P W g R (θ ω) - D - R (obs ψ g θ W ξ t ω).2|) ∂P ≠ ⊤)
    (hgood : ∫ ω, supReward P W g R (θ ω) ∂P - D ≤ ∫ ω, meanReward g R (P.map (W 0)) (Ã ω) (θ ω) ∂P) :
    Summable (fun t => α ^ t * (∫ ω, meanReward g R (P.map (W 0)) (Ã ω) (θ ω) ∂P
        - ∫ ω, R (obs ψ g θ W ξ t ω).2 ∂P)) ∧
      sRegret P θ W ξ g R ψ α D ≤
        ∑' t, α ^ t * (∫ ω, meanReward g R (P.map (W 0)) (Ã ω) (θ ω) ∂P
          - ∫ ω, R (obs ψ g θ W ξ t ω).2 ∂P) := by sorry

end SatisficingTS
