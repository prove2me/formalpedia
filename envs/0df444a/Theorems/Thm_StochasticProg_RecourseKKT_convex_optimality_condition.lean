-- Prove2me | Theorems.Thm_StochasticProg_RecourseKKT_convex_optimality_condition
-- name    : StochasticProg.RecourseKKT.convex_optimality_condition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:54:00.371519+00:00
-- url     : https://prove2.me/theorems/a215a502-feeb-48cb-b021-198af7e1a261
-- title:
--   Optimality of a convex function over $K_1$ via subgradients (proof of Theorem 9) (corrected: regularity condition on the only-if direction)
-- statement:
--   Assume that $\xi$ has finite second moments, that $Q(x,\xi) \ne -\infty$ for every $x$ almost surely, and that (1.2) has a finite optimal value. Let $x^* \in K_1$ and $z(x) = c^{\mathsf T}x + \mathcal Q(x)$.
--
--   1. If $z$ has a subgradient $\eta$ at $x^*$ with $\eta^{\mathsf T}(x - x^*) \ge 0$ for all $x \in K_1$, then $x^*$ minimizes $z$ over $K_1$.
--   2. **(corrected)** Assume the regularity condition
--
--      (R) $K_1 \cap \operatorname{ri} K_2 \ne \emptyset$, or $K_2$ is a convex polyhedron, or $K_1 \subseteq K_2$ (relatively complete recourse).
--
--      If $x^*$ minimizes $z$ over $K_1$, then $z$ has a subgradient $\eta$ at $x^*$ with
--   $$
--   \eta^{\mathsf T}(x - x^*) \ge 0 \qquad \text{for all } x \in K_1 .
--   $$
--
--   The book states the equivalence without (R), citing Bazaraa and Shetty [1979, Theorem 3.4.3], a theorem for convex functions finite on all of $\mathbb R^n$; here $z = +\infty$ off $K_2$, and the "only if" direction fails without a regularity condition (see below). Each case of (R) is one the book itself uses: finite $\xi$ (Theorem 1(b)), fixed $T$ (Theorem 5(b)), relatively complete recourse (Corollary 12).
--
--   **Formalization Note** $\operatorname{ri}$ is the relative interior (`intrinsicInterior`).
--
--   Differences from the source:
--   - correction: 'only if': x* minimizes cᵀx + 𝒬(x) over K₁ ⇒ a subgradient η at x* with ηᵀ(x − x*) ≥ 0 on K₁, with no further condition → the 'only if' direction assumes (R): K₁ ∩ ri K₂ ≠ ∅, or K₂ polyhedral, or K₁ ⊆ K₂; reason: false as printed. Counterexample satisfying every assumption of the book: n1 = 2, A = [1 0], b = 0 (K₁ = {(0, s) | s ≥ 0}), c = (0, 1), W = [1], q ≡ 0, θ uniform on [0, 2π), T(θ) = [cos θ, sin θ], h(θ) = cos θ + sin θ + 1: K₂ is the closed disc of centre (1, 1) and radius 1, x* = (0, 1) is optimal with value 1, ∂𝒬(x*) = {(−t, 0) | t ≥ 0}, so every subgradient of the objective at x* is (−t, 1), and ηᵀ((0, 0) − x*) = −1 < 0
--   - generalization: Q(x, ξ) is not −∞ (for every x and ξ, p. 112) → for every x, Q(x, ξ(ω)) ≠ −∞ for P-almost every ω; reason: a weaker hypothesis, implied by the book's; null events do not affect 𝒬 (p. 110)
--   - encoding: ξ has finite second moments → every coordinate of q, h, T is in L²(P); reason: equivalent to E‖ξ‖² < ∞
--   - encoding: ∂f(x) = {η | f(w) ≥ f(x) + ηᵀ(w − x) ∀w} → subdifferential with f(x) required real (empty where f(x) = ±∞); reason: the convex-analysis convention for extended-valued functions; at points where 𝒬 is finite it is the book's set
--   - encoding: 𝒬(x) = E_ξ Q(x, ξ) with +∞ + (−∞) = +∞ and 0·∞ = 0 → EReal value: +∞ if ∫⁻ Q⁺ = ∞, else ∫⁻ Q⁺ − ∫⁻ Q⁻; reason: the book's convention written out; same instances
-- source:
--   Birge & Louveaux, Introduction to Stochastic Programming, 2nd ed., Springer 2011, doi:10.1007/978-1-4614-0237-4, Chapter 3, §3.1e, proof of Theorem 9, first sentence, printed p. 116 (PDF p. 141)

import Mathlib
import Definitions.Def_StochasticProg_RecourseKKT_RecourseData
import Definitions.Def_StochasticProg_RecourseKKT_expectedRecourse
import Definitions.Def_StochasticProg_RecourseKKT_firstStageSet
import Definitions.Def_StochasticProg_RecourseKKT_secondStageFeasSet
import Definitions.Def_StochasticProg_RecourseKKT_depObjective
import Definitions.Def_StochasticProg_RecourseKKT_IsOptimalDEP
import Definitions.Def_StochasticProg_RecourseKKT_HasFiniteOptimalValue
import Definitions.Def_StochasticProg_RecourseKKT_FiniteSecondMoments
import Definitions.Def_StochasticProg_RecourseKKT_RecourseNotNegInf
import Definitions.Def_StochasticProg_RecourseKKT_subdifferential
import Definitions.Def_StochasticProg_RecourseKKT_IsPolyhedralSet
open MeasureTheory Matrix

namespace StochasticProg.RecourseKKT

/-- **Optimality condition for a convex function over `K₁` (proof of Theorem 9), corrected.**
Birge & Louveaux, *Introduction to Stochastic Programming*, 2nd ed., Springer 2011,
doi:10.1007/978-1-4614-0237-4, Chapter 3, §3.1e, proof of Theorem 9, printed p. 116 (PDF p. 141): "From the optimization of
a convex function over a convex region (see, for example, Bazaraa and Shetty [1979, Theorem 3.4.3]),
we have that cᵀx + 𝒬(x) has a subgradient η at x* such that ηᵀ(x − x*) ≥ 0 for all x ∈ K₁ if and
only if x* minimizes cᵀx + 𝒬(x) over K₁."

Under the hypotheses of Theorem 9 (finite second moments, `Q ≠ −∞`, finite optimal value of (1.2))
and `x* ∈ K₁`:
(i) if `cᵀx + 𝒬(x)` has a subgradient `η` at `x*` with `ηᵀ(x − x*) ≥ 0` for all `x ∈ K₁`, then
`x*` is optimal;
(ii) **(corrected)** if moreover the regularity condition (R) holds —
`K₁ ∩ ri K₂ ≠ ∅`, or `K₂` is a convex polyhedron, or `K₁ ⊆ K₂` — and `x*` is optimal, then such a
subgradient exists.

**Formalization Note (correction).** The "only if" is false as printed: with `n1 = 2`,
`K₁ = {(0, s) | s ≥ 0}` (`A = [1 0]`, `b = 0`), `c = (0, 1)`, `W = [1]`, `q ≡ 0`, `θ` uniform on
`[0, 2π)`, `T(θ) = [cos θ, sin θ]`, `h(θ) = cos θ + sin θ + 1`, the set `K₂` is the closed disc of
centre `(1, 1)` and radius `1`, `x* = (0, 1)` is optimal, and every subgradient of `cᵀx + 𝒬(x)` at
`x*` is `(−t, 1)` with `t ≥ 0`, which fails `ηᵀ(x − x*) ≥ 0` at `x = (0, 0)`. The cited Bazaraa–Shetty
theorem is for functions finite on all of `ℜⁿ`. (R) is assumed on the "only if" direction only;
each disjunct is a case the book uses (finite `ξ`, Theorem 1(b); fixed `T`, Theorem 5(b); relatively
complete recourse, Corollary 12). `ri` is `intrinsicInterior`. -/
theorem convex_optimality_condition {Ω : Type*} [MeasurableSpace Ω] {n1 m1 n2 m2 : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (pb : RecourseData Ω n1 m1 n2 m2)
    (hmom : FiniteSecondMoments P pb) (hnn : RecourseNotNegInf P pb)
    (hfin : HasFiniteOptimalValue P pb)
    (xs : Fin n1 → ℝ) (hxs : xs ∈ firstStageSet pb.A pb.b) :
    ((∃ η ∈ subdifferential (depObjective P pb) xs,
        ∀ x ∈ firstStageSet pb.A pb.b, 0 ≤ η ⬝ᵥ (x - xs)) → IsOptimalDEP P pb xs) ∧
      (((firstStageSet pb.A pb.b ∩ intrinsicInterior ℝ (secondStageFeasSet P pb)).Nonempty ∨
          IsPolyhedralSet (secondStageFeasSet P pb) ∨
          firstStageSet pb.A pb.b ⊆ secondStageFeasSet P pb) →
        IsOptimalDEP P pb xs →
          ∃ η ∈ subdifferential (depObjective P pb) xs,
            ∀ x ∈ firstStageSet pb.A pb.b, 0 ≤ η ⬝ᵥ (x - xs)) := by sorry

end StochasticProg.RecourseKKT
