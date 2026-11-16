-- Prove2me | Theorems.Thm_RobustCtxPricing_Supplement_theorem_3_8
-- name    : RobustCtxPricing.Supplement.theorem_3_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:05:01.206296+00:00
-- url     : https://prove2.me/theorems/2a792e9d-d60a-4039-b55d-332d2fc0c3d0
-- title:
--   Theorem 3.8 — with proximity feedback, Algorithm 1 has regret $O(Cd+d\log T)$
-- statement:
--   There is an absolute constant $K$ such that the following holds. Let $d\ge1$ be the context dimension, $T\ge2$ the horizon and $C\in\mathbb N$ the corruption budget. Let $\theta^\star\in\Theta=\mathcal B_d(0,1)$ and let $u_1,\dots,u_T\in\Theta$ be any contexts with valuations $v_t=\langle\theta^\star,u_t\rangle\ge0$. Run Algorithm 1 with $\bar C=C$ and $\epsilon=T^{-3}$, under any tie-breaking, against proximity feedback $X_t$ and sale feedback $Y_t$ such that, outside a set of at most $C$ rounds, $X_t=\mathbb I\{|p_t-v_t|\le\epsilon\}$ and $Y_t=\mathbb I\{p_t\le v_t\}$. Then
--   $$
--   R_T=\sum_{t=1}^T\big(v_t-p_t\,\mathbb I\{p_t\le v_t\}\big)\le K\,\big(Cd+d\log T\big).
--   $$
--   With the stronger proximity feedback the regret is linear in $C$ and only $d\log T$ in the horizon; this is the warm-up of the paper's approach, which Theorem 4.2 extends to sale feedback alone at the price of a factor $d$ on $\log T$.
--
--   Differences from the source:
--   - reading: R_T = O(Cd + d log T) → ∃ K absolute, ∀ d ≥ 1, T ≥ 2, C, θ⋆, contexts, feedback and runs: R_T ≤ K(Cd + d log T); reason: at T = 1 the literal bound K·Cd fails (d = 1, C = 0, θ⋆ = u_1 = e₁: the single round explores at price 0 and R_1 = 1); the same reading as the published Theorem 4.2
--   - reading: "X_t = x_t for every t ∉ S, while for t ∈ S, the corrupted signals X_t, Y_t may be chosen arbitrarily" (p.12) → one set S, |S| ≤ C, outside which both X_t = 𝕀{|p_t − v_t| ≤ ϵ} and Y_t = 𝕀{p_t ≤ v_t}; reason: the sale bit is corrupted only on S by §2.2, which §3 keeps ("in addition to the feedback Y_t"), and the page names X_t, Y_t together as the signals that are arbitrary on S
--   - generalization: Algorithm 1 (no tie-breaking fixed) → every run under every tie-break: any solution of (3), any non-predicting receiving set, any coefficients satisfying (1); reason: specializes to any fixed rule
--   - encoding: the adaptive adversary → all context and feedback sequences (u, X, Y), with the corruption constraint evaluated on the run's own prices; reason: the run is determined by the contexts, the feedback and the tie-breaking choices
--   - encoding: rounds t = 1, …, T and bits in {0, 1} → rounds 0, …, T − 1 of ℕ-indexed sequences and Bool bits; reason: Lean convention; same instances
--   - reading: 𝓑_d(0,1), "the d-dimensional Euclidean ball" → the closed unit ball of EuclideanSpace ℝ (Fin d); reason: the analysis uses ‖u_t‖₂ ≤ 1 and ‖θ⋆‖₂ ≤ 1 (pp.18, 21); this is the published base model's convention
--   - reading: the budget C (its type is not stated) → C ∈ ℕ; reason: it bounds the number |S| of corrupted rounds
--   - reading: log → the natural logarithm Real.log; reason: the base is not stated; natural log is the standard meaning and the constants of the proofs hold with it
--   - encoding: the test (1), min_λ {…} ≤ 1/(8T) → ∃ λ with ϵ‖λ‖₁ + ‖u − Σ λ_i u_i‖₂ ≤ 1/(8T) (published Predicts); reason: for ϵ > 0 the objective is continuous and coercive, so the minimum is attained and the two tests agree
--   - encoding: the cases of Update-Density overlap on the hyperplanes ⟨u_t, θ⟩ = m_t ± ϵ/2 → the window case takes priority there (published updateDensity); reason: the page leaves the overlap open; for u_t ≠ 0 the hyperplanes are Lebesgue-null
--   - encoding: evidence sets 𝓗_1, …, 𝓗_{2C̄+1}, C̄ = C → lists of samples in insertion order indexed by Fin (2C + 1) (published Run); reason: Lean convention; same instances
--   - encoding: "(C̄ + 1)-st largest lower endpoint" → the entry with index C̄ of the lower endpoints sorted non-increasingly (published commitPrice); reason: Lean convention; same instances
-- source:
--   Castiglioni and Stradi, Decoupling Corruption and Horizon in Robust Contextual Pricing, arXiv:2607.11210, Theorem 3.8, p.19 (Algorithm 1, p.12; proximity feedback and corruption, pp.11–12; model §2, pp.10–11)

import Mathlib
import Definitions.Def_RobustCtxPricing_Model
import Definitions.Def_RobustCtxPricing_Evidence
import Definitions.Def_RobustCtxPricing_Density
import Definitions.Def_RobustCtxPricing_Algorithm4
import Definitions.Def_RobustCtxPricing_Supplement_Algorithm1

namespace RobustCtxPricing.Supplement

/-- **Theorem 3.8.** Castiglioni–Stradi, *Decoupling Corruption and Horizon in Robust Contextual
Pricing*, arXiv:2607.11210, §3.2.4, p.19: "Algorithm 1 attains regret: `R_T = O(Cd + d log T)`."

There is an absolute constant `K` such that for every dimension `d ≥ 1`, horizon `T ≥ 2`,
corruption budget `C ∈ ℕ`, parameter `θ⋆ ∈ Θ`, context sequence `u_1, …, u_T ∈ Θ` with valuations
`v_t = ⟨θ⋆, u_t⟩ ≥ 0`, observed proximity and sale feedback `X`, `Y`, and run of Algorithm 1
(horizon `T`, corruption parameter `C̄ = C`, `ϵ = T⁻³`, any tie-breaking) such that, outside a set
of at most `C` rounds, `X_t = 𝕀{|p_t − v_t| ≤ ϵ}` and `Y_t = 𝕀{p_t ≤ v_t}`, the regret satisfies
`R_T ≤ K (Cd + d log T)`.

**Formalization Note.** `O(·)` is "`∃ K` absolute, quantified before every other variable"; it is
read for `T ≥ 2` (at `T = 1` the bound is `K·Cd`, which fails for `C = 0`: `d = 1`, `θ⋆ = u_1 = 1`
explores at price `0` and `R_1 = 1`). "In this section, `C̄ = C`" (p.12). The adaptive adversary
is covered by quantifying over all `(u, X, Y)` and all runs, with the corruption constraint
evaluated on the run's own prices. `log` is natural. -/
theorem theorem_3_8 : ∃ K : ℝ, ∀ (d T C : ℕ), 1 ≤ d → 2 ≤ T →
    ∀ θ : EuclideanSpace ℝ (Fin d), θ ∈ Theta d →
    ∀ u : ℕ → EuclideanSpace ℝ (Fin d), (∀ t < T, u t ∈ Theta d) →
      (∀ t < T, 0 ≤ inner ℝ θ (u t)) →
    ∀ (X Y : ℕ → Bool) (r : Run d (2 * C + 1)),
      IsAlg1Run T C u X Y r → IsCorruptedXY T C (epsT T) θ u r.p X Y →
      regret T θ u r.p ≤ K * ((C : ℝ) * d + (d : ℝ) * Real.log T) := by sorry

end RobustCtxPricing.Supplement
