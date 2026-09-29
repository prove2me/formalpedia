-- Prove2me | Theorems.Thm_StochasticProg_Bounds_thm1_jensen_partition_lower_bound
-- name    : StochasticProg.Bounds.thm1_jensen_partition_lower_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-18T04:54:46.716158+00:00
-- url     : https://prove2.me/theorems/c7aa48b5-af34-4aae-b45b-9649ac4ae3c9
-- title:
--   Chapter 8, Theorem 1 — finite-partition Jensen lower bound
-- statement:
--   **Chapter 8, Theorem 1** (Birge & Louveaux, p. 346): the finite-partition Jensen lower bound.
--
--   Fix a probability space $(\Omega,\mu)$, a complete normed real vector space $E$, a closed
--   convex set $\Xi\subseteq E$, and a random vector $\xi:\Omega\to E$ with $\xi(\omega)\in\Xi$
--   almost surely and $\xi$ Bochner-integrable. Fix a type $\alpha$ of first-stage decisions, a set
--   $D\subseteq\alpha$, a point $x\in D$, and a function $g:\alpha\to E\to\mathbb R$ such that
--   $g(x,\cdot)$ is convex and continuous on $\Xi$, with $\omega\mapsto g(x,\xi(\omega))$
--   integrable. Fix a finite measurable partition $P$ of $\Omega$ into $\nu$ blocks (in the sense
--   of the companion `Partition` definition), with block weights $p_l=P.\mathrm{weight}(l)$ and
--   block conditional means $\xi^l = P.\mathrm{condMean}(\xi,l)$. Then
--   $$
--   \sum_{l=1}^{\nu} p_l\, g(x,\xi^l) \;\le\; \int_\Omega g(x,\xi(\omega))\,d\mu(\omega) ,
--   $$
--   i.e. $\sum_l p_l\,g(x,\xi^l) \le \mathbb E(g(x))$ — the book's inequality (2.1), read
--   left-to-right as printed (the book states $\mathbb E(g(x)) \ge \sum_l p_l g(x,\xi^l)$).
--
--   **Formalization Note** Two hypotheses are added beyond the book's bare statement, both needed
--   for the underlying Mathlib integral-Jensen lemma rather than narrowings of the content:
--   `ContinuousOn (g x) Ξ` (automatic for a convex function on the interior of a
--   finite-dimensional domain, but $E$ is not assumed finite-dimensional here) and integrability
--   of $\xi$ and of $\omega\mapsto g(x,\xi(\omega))$ (needed for $\mathbb E(g(x))$ and each
--   $\xi^l$ to be well-defined). $\xi^l$ is exactly the conditional mean `Partition.condMean`,
--   never an arbitrary point of the block.
-- source:
--   Birge & Louveaux, Introduction to Stochastic Programming, 2nd ed., Springer 2011, p. 346, Chapter 8, Theorem 1 (eq. 2.1)

import Mathlib
import Definitions.Def_StochasticProg_Bounds_Partition

open MeasureTheory

namespace StochasticProg.Bounds

variable {Ω E α : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Chapter 8, Theorem 1 (Birge & Louveaux, p. 346): the finite-partition Jensen lower bound.
For `g(x, ·)` convex on the (convex, closed) support `Ξ` of a random vector `ξ`, and a finite
measurable partition of the sample space into blocks `S_l` of probability `p_l = P[ξ ∈ S_l]`
with conditional means `ξ^l = E[ξ | S_l]`,
`E(g(x)) ≥ Σ_{l=1}^ν p_l g(x, ξ^l)`. -/
theorem thm1_jensen_partition_lower_bound
    {Ξ : Set E} (hΞconv : Convex ℝ Ξ) (hΞclosed : IsClosed Ξ)
    {ξ : Ω → E} (hξrange : ∀ᵐ ω ∂μ, ξ ω ∈ Ξ) (hξint : Integrable ξ μ)
    {D : Set α} {x : α} (hx : x ∈ D) {g : α → E → ℝ}
    (hgconv : ConvexOn ℝ Ξ (g x)) (hgcont : ContinuousOn (g x) Ξ)
    (hgint : Integrable (fun ω => g x (ξ ω)) μ)
    {ν : ℕ} (P : Partition μ ν) :
    ∑ l, P.weight l * g x (P.condMean ξ l) ≤ ∫ ω, g x (ξ ω) ∂μ := by sorry

end StochasticProg.Bounds
