-- Prove2me | Theorems.Thm_SatisficingTS_tsum_discounted_gap_le_sqrt_mul_sqrt
-- name    : SatisficingTS.tsum_discounted_gap_le_sqrt_mul_sqrt
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:25:27.747348+00:00
-- url     : https://prove2.me/theorems/46177a06-dca8-475d-b200-d1051dc3722b
-- title:
--   Proof of Theorem 1, p.9 — Cauchy–Schwarz: $\sum_t\alpha^t\,\mathbb E[\tilde R-R_t]\le\sqrt{\sum_t\alpha^{2t}\Gamma_t}\,\sqrt{\sum_t I(\tilde A;(A_t,Y_t)\mid\mathcal H_{t-1})}$
-- statement:
--   Let $\psi$ be any policy, $\tilde A$ any action-valued random variable and $\alpha$ any real number, and write $\Gamma_t$ for the single-period information ratio and $I_t=I\bigl(\tilde A;(A_t,Y_t)\mid\mathcal H_{t-1}\bigr)$. If
--   $$
--   \sum_{t=0}^\infty\alpha^{2t}\Gamma_t<\infty\qquad\text{and}\qquad\sum_{t=0}^\infty I_t<\infty,
--   $$
--   then the series $\sum_t\alpha^t\bigl(\mathbb E[\tilde R]-\mathbb E[R_t]\bigr)$ converges and
--   $$
--   \sum_{t=0}^{\infty}\alpha^{t}\bigl(\mathbb E[\tilde R]-\mathbb E[R_t]\bigr)\ \le\ \sqrt{\sum_{t=0}^{\infty}\alpha^{2t}\Gamma_t}\ \sqrt{\sum_{t=0}^{\infty}I_t}.
--   $$
--
--   This is the Cauchy–Schwarz step of Theorem 1: it converts the per-period information ratios and the information budget into a bound on the discounted shortfall.
--
--   **Formalization Note** $\Gamma_t$ is the ratio in $[0,\infty]$ with $x/0=\infty$ for $x>0$ and $0/0=0$; the two series are sums in $[0,\infty]$, converted to real numbers after the finiteness hypotheses.
--
--   Differences from the source:
--   - reading: ∑ α^t E[R̃ − R_t] = ∑ √(α^{2t}Γ_t) √(I_t) ≤ √(∑ α^{2t}Γ_t) √(∑ I_t) → ∑ α^t (E[R̃] − E[R_t]) ≤ √(∑ α^{2t}Γ_t) √(∑ I_t); reason: the intermediate equality fails for a term with E[R̃ − R_t] < 0 (then the left term is negative and the right one is not); the net inequality, which the proof uses, holds
--   - generalization: under the hypotheses of Theorem 1, α ∈ [0,1] → any processes θ, W, ξ, any ψ, g, R, any random action Ã, any real α; only the two series finite; reason: the step is algebraic; the paper's setting is a special case
--   - generalization: the series on the left → also asserts that it converges; reason: extra conclusion
--   - encoding: ∑ α^{2t}Γ_t and ∑ I_t (finite in the proof: ∑ I_t ≤ I(Ã;θ) < ∞, Γ < ∞) → hypotheses that both [0,∞] sums are ≠ ⊤; reason: excludes only the cases where the printed right side is undefined or infinite
--   - encoding: E[R̃ − R_t] → E[R̃] − E[R_t]; reason: equal under integrability; the same expression is used inside Γ_t
--   - encoding: action set A and outcome set Y arbitrary → standard Borel, nonempty measurable spaces; reason: the conditional mutual information I(·;·|H_{t−1}) needs regular conditional distributions (published condMutualInfo); finite, countable and Euclidean action/outcome sets are all standard Borel
-- source:
--   Russo & Van Roy, Satisficing in Time-Sensitive Bandit Learning, arXiv:1803.02855v2, proof of Theorem 1, p.9, lines 2–3 of the chain ("where the first inequality follows from the Cauchy-Schwarz inequality")

import Mathlib
import Definitions.Def_ThompsonTutorial_InfoRatio_condMutualInfo
import Definitions.Def_SatisficingTS_obs
import Definitions.Def_SatisficingTS_hist
import Definitions.Def_ThompsonTutorial_InfoRatio_meanReward
import Definitions.Def_SatisficingTS_infoRatioTerm
open MeasureTheory ThompsonTutorial.InfoRatio
open scoped ENNReal

namespace SatisficingTS

/-- **The Cauchy–Schwarz step** (Russo & Van Roy, *Satisficing in Time-Sensitive Bandit Learning*,
arXiv:1803.02855v2, proof of Theorem 1, p.9, lines 2–3 of the chain:
`∑ α^t E[R̃ − R_t] = ∑ √(α^{2t}Γt) √(I(Ã; (At, Yt)|Ht−1)) ≤ √(∑ α^{2t}Γt) √(∑ I(Ã; (At, Yt)|Ht−1))`,
"where the first inequality follows from the Cauchy-Schwarz inequality").

For any policy `ψ`, any action-valued random variable `Ã` and any real `α`, if
`∑_t α^{2t} Γ_t < ∞` and `∑_t I(Ã; (A_t, Y_t) | H_{t−1}) < ∞`, then the series
`∑_t α^t (E[R̃] − E[R_t])` converges and
`∑_{t=0}^∞ α^t (E[R̃] − E[R_t]) ≤ √(∑_t α^{2t} Γ_t) · √(∑_t I(Ã; (A_t, Y_t) | H_{t−1}))`.

**Formalization Note.** `Γ_t = infoRatioTerm … t` is the `ℝ≥0∞` ratio `(E[R̃] − E[R_t])² / I_t`
(`x/0 = ⊤` for `x > 0`, `0/0 = 0`); the two series are `ℝ≥0∞` sums, converted to reals after the
finiteness hypotheses. The printed "=" is "≤" in general (a term with `E[R̃ − R_t] < 0`). -/
theorem tsum_discounted_gap_le_sqrt_mul_sqrt
    {Ω Θ 𝒲 Ξ 𝒜 𝒴 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒲]
    [MeasurableSpace 𝒜] [StandardBorelSpace 𝒜] [Nonempty 𝒜]
    [MeasurableSpace 𝒴] [StandardBorelSpace 𝒴] [Nonempty 𝒴]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (θ : Ω → Θ) (W : ℕ → Ω → 𝒲) (ξ : Ω → Ξ) (g : 𝒜 → Θ → 𝒲 → 𝒴) (R : 𝒴 → ℝ)
    (ψ : (t : ℕ) → (Fin t → 𝒜 × 𝒴) → Ξ → 𝒜) (Ã : Ω → 𝒜) (α : ℝ)
    (hΓ : ∑' t, ENNReal.ofReal (α ^ (2 * t)) * infoRatioTerm P θ W ξ g R ψ Ã t ≠ ⊤)
    (hI : ∑' t, condMutualInfo P Ã (obs ψ g θ W ξ t) (hist ψ g θ W ξ t) ≠ ⊤) :
    Summable (fun t => α ^ t * (∫ ω, meanReward g R (P.map (W 0)) (Ã ω) (θ ω) ∂P
        - ∫ ω, R (obs ψ g θ W ξ t ω).2 ∂P)) ∧
      ∑' t, α ^ t * (∫ ω, meanReward g R (P.map (W 0)) (Ã ω) (θ ω) ∂P
          - ∫ ω, R (obs ψ g θ W ξ t ω).2 ∂P) ≤
        Real.sqrt (∑' t, ENNReal.ofReal (α ^ (2 * t)) * infoRatioTerm P θ W ξ g R ψ Ã t).toReal *
          Real.sqrt (∑' t, condMutualInfo P Ã (obs ψ g θ W ξ t) (hist ψ g θ W ξ t)).toReal := by sorry

end SatisficingTS
