-- Prove2me | Theorems.Thm_Supermodularity_MDP_stochastically_supermodular_iff_integral_supermodular
-- name    : Supermodularity.MDP.stochastically_supermodular_iff_integral_supermodular
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-19T21:28:59.371459+00:00
-- url     : https://prove2.me/theorems/5e60d092-1f97-48aa-b322-5d88efe355a2
-- title:
--   Corollary 3.9.1(b) - stochastic supermodularity via increasing integrands
-- statement:
--   Let $T \subseteq \mathbb{R}^m$ be a sublattice, and let $\{F(t,\cdot) : t \in T\}$ be a family
--   of probability distributions on $\mathbb{R}^n$ (represented by probability measures $\mu_t$).
--
--   Then $\{F(t,\cdot)\}$ is **stochastically supermodular** in $t$ on $T$ if and only if
--   $$
--   \int h(w)\, dF(t,w)
--   $$
--   is a supermodular function of $t$ on $T$ for every increasing real-valued function $h$ on
--   $\mathbb{R}^n$ (integrable against every $\mu_t$).
--
--   This is part (b) of Topkis's Corollary 3.9.1, the special case of Theorem 3.9.1 obtained by
--   taking $V$ to be the closed convex cone of supermodular functions on $T$. It is what Theorem
--   3.9.2 invokes to pass from "the transition law is stochastically supermodular" to
--   "$\int f_{i+1}(w)\, dF(x,t,i,w)$ is supermodular in $(x,t)$".
--
--   **Formalization Note.** Only the supermodular half of Corollary 3.9.1 (part (b)) is
--   formalized, since it is the only part Theorem 3.9.2's proof uses; parts (a) (stochastic
--   monotonicity) and (c) (stochastic convexity) are left out of this mission's scope.
-- source:
--   Topkis, Supermodularity and Complementarity, Princeton University Press, 2011, p. 161, Corollary 3.9.1(b)

import Mathlib
import Definitions.Def_Supermodularity_MDP_StochasticallySupermodularOn
import Definitions.Def_Supermodularity_Monotonicity_SupermodularOn

open MeasureTheory

namespace Supermodularity.MDP

/-- Corollary 3.9.1(b) (p. 161, PDF 174). If `T` is a sublattice of `Rᵐ`, then
`{F(t,w) : t ∈ T}` is stochastically supermodular (submodular) in `t` on `T` iff
`∫ h(w) dF(t,w)` is supermodular (submodular) in `t` on `T` for every increasing
real-valued function `h` on `Rⁿ`. Only the supermodular half is formalized, as
Theorem 3.9.2 invokes. -/
theorem stochastically_supermodular_iff_integral_supermodular {m n : ℕ}
    (T : Set (Fin m → ℝ)) (hT : IsSublattice T)
    (μ : (Fin m → ℝ) → Measure (Fin n → ℝ))
    (hμ : ∀ t, IsProbabilityMeasure (μ t)) :
    StochasticallySupermodularOn T μ ↔
      (∀ ⦃h : (Fin n → ℝ) → ℝ⦄, Monotone h →
        (∀ t ∈ T, Integrable h (μ t)) →
        Supermodularity.Monotonicity.SupermodularOn (fun t => ∫ w, h w ∂ (μ t)) T) := by sorry

end Supermodularity.MDP
