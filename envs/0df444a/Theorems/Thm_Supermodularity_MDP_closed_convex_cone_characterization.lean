-- Prove2me | Theorems.Thm_Supermodularity_MDP_closed_convex_cone_characterization
-- name    : Supermodularity.MDP.closed_convex_cone_characterization
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-19T21:27:16.982714+00:00
-- url     : https://prove2.me/theorems/5259d055-5ef3-4bf7-851d-354baf3b8831
-- title:
--   Theorem 3.9.1 - closed convex cone characterization of the integral
-- statement:
--   Let $T \subseteq \mathbb{R}^m$, let $\{F(t,\cdot) : t \in T\}$ be a family of distribution
--   functions on $\mathbb{R}^n$ (represented by measures $\mu_t$), and let $V$ be a set of
--   real-valued functions on $T$ that is a **closed convex cone**: closed in the topology of
--   pointwise convergence on $T \to \mathbb{R}$, closed under addition, and closed under
--   multiplication by nonnegative scalars.
--
--   Then the following are equivalent:
--
--   1. $\int_S dF(t,w) \in V$ (as a function of $t \in T$) for every increasing set
--      $S \subseteq \mathbb{R}^n$.
--   2. $\int h(w)\, dF(t,w) \in V$ (as a function of $t \in T$) for every increasing real-valued
--      function $h$ on $\mathbb{R}^n$.
--
--   This is Topkis's Theorem 3.9.1. It generalizes Lehmann's [1955] characterization of stochastic
--   monotonicity (the case $V$ = increasing functions) to any property of $t \mapsto
--   \int h\,dF(t,w)$ whose defining set of functions is a closed convex cone, in particular
--   supermodularity and convexity/concavity in $t$ (Corollary 3.9.1).
--
--   **Formalization Note.** $\int h(w)\,dF(t,w)$ is the Bochner integral of $h$ against $\mu_t$;
--   since $h$ need not be bounded, integrability of $h$ against every $\mu_t$ is supplied as an
--   explicit hypothesis (direction 2 only needs it where it concludes membership in $V$).
-- source:
--   Topkis, Supermodularity and Complementarity, Princeton University Press, 2011, p. 159-160, Theorem 3.9.1

import Mathlib

open MeasureTheory

namespace Supermodularity.MDP

/-- Theorem 3.9.1 (p. 159–160, PDF 172–173). `T` is a subset of `Rᵐ`, `{F(t,w) : t ∈ T}`
is a collection of distribution functions on `Rⁿ` (represented by measures `μ t`), and `V`
is a closed (in the topology of pointwise convergence on `T → ℝ`) convex cone of
real-valued functions on `T`. Then `∫_S dF(t,w) ∈ V` for every increasing set `S ⊆ Rⁿ` iff
`∫ h(w) dF(t,w) ∈ V` for every increasing real-valued `h` on `Rⁿ`. -/
theorem closed_convex_cone_characterization {m n : ℕ} (T : Set (Fin m → ℝ))
    (μ : (Fin m → ℝ) → Measure (Fin n → ℝ)) (V : Set (T → ℝ))
    (hVclosed : IsClosed V)
    (hVadd : ∀ ⦃f g : T → ℝ⦄, f ∈ V → g ∈ V → f + g ∈ V)
    (hVsmul : ∀ ⦃f : T → ℝ⦄, f ∈ V → ∀ ⦃c : ℝ⦄, 0 ≤ c → c • f ∈ V) :
    (∀ ⦃S : Set (Fin n → ℝ)⦄, IsUpperSet S →
        (fun t : T => (μ (t : Fin m → ℝ) S).toReal) ∈ V) ↔
      (∀ ⦃h : (Fin n → ℝ) → ℝ⦄, Monotone h →
        (∀ t : T, Integrable h (μ (t : Fin m → ℝ))) →
        (fun t : T => ∫ w, h w ∂ (μ (t : Fin m → ℝ))) ∈ V) := by sorry

end Supermodularity.MDP
