-- Prove2me | Theorems.Thm_StochasticProg_RecourseKKT_theorem_1
-- name    : StochasticProg.RecourseKKT.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:49:37.049988+00:00
-- url     : https://prove2.me/theorems/3c790055-b16d-4636-8b1f-87b5ae5e36cf
-- title:
--   Theorem 1 — the feasibility sets $K_2(\xi)$ and, for finite $\xi$, $K_2$ are convex polyhedra
-- statement:
--   Consider a two-stage stochastic linear program with fixed recourse matrix $W$ and random data $\xi = (q, h, T)$ on a probability space $(\Omega, \mathcal F, P)$.
--
--   1. For every realization $(h, T)$ (and every recourse matrix $W$), the elementary feasibility set $K_2(\xi) = \{x \mid \exists\, y \ge 0,\ Wy = h - Tx\}$ is a convex polyhedron.
--   2. If $\xi$ is a finite discrete random variable, that is, $\xi(\omega)$ lies almost surely in a finite set, then
--   $$
--   K_2 = \{\, x \mid \mathcal Q(x) < \infty \,\}
--   $$
--   is a convex polyhedron.
--
--   Part 2 is the finite-distribution case of the regularity condition under which the corrected Theorem 9 holds: there $K_2$ is polyhedral.
--
--   Differences from the source:
--   - reading: (b) K₂ = ⋂_{ξ∈Ξ} K₂(ξ) (p. 106) → (b) K₂ = {x | 𝒬(x) < ∞} (secondStageFeasSet, p. 109); reason: for a finite discrete ξ the two agree up to realizations of probability zero, which the book ignores (p. 110); this is the K₂ of Theorem 9
--   - encoding: ξ is a finite discrete random variable → ξ lies almost surely in a finite set; reason: the same distributions; events of probability zero are ignored (p. 110)
--   - encoding: convex polyhedron → finite intersection of half-spaces {φᵢ(x) ≤ uᵢ}; reason: the standard definition; ∅ and the whole space are polyhedra, as in the book's proof of Theorem 5(b)
-- source:
--   Birge & Louveaux, Introduction to Stochastic Programming, 2nd ed., Springer 2011, doi:10.1007/978-1-4614-0237-4, Chapter 3, §3.1b, Theorem 1, printed p. 106 (PDF p. 131)

import Mathlib
import Definitions.Def_StochasticProg_RecourseKKT_RecourseData
import Definitions.Def_StochasticProg_RecourseKKT_elementaryFeasSet
import Definitions.Def_StochasticProg_RecourseKKT_secondStageFeasSet
import Definitions.Def_StochasticProg_RecourseKKT_IsPolyhedralSet
open MeasureTheory

namespace StochasticProg.RecourseKKT

/-- **Theorem 1 (polyhedrality of the feasibility sets).**
Birge & Louveaux, *Introduction to Stochastic Programming*, 2nd ed., Springer 2011,
doi:10.1007/978-1-4614-0237-4, Chapter 3, §3.1b, Theorem 1, printed p. 106 (PDF p. 131):
"a. For a given ξ, the elementary feasibility set K₂(ξ) is a convex polyhedron.
b. When ξ is a finite discrete random variable, K₂ is a convex polyhedron."

(a) For every recourse matrix `W` and every realization `(h, T)`, `K₂(ξ)` is a convex polyhedron.
(b) If `ξ = (q, h, T)` takes, almost surely, only finitely many values, then
`K₂ = {x | 𝒬(x) < ∞}` is a convex polyhedron.

**Formalization Note.** In (b) the book's `K₂ = ⋂_{ξ ∈ Ξ} K₂(ξ)` (p. 106) is stated for the
general definition `K₂ = {x | 𝒬(x) < ∞}` of p. 109 (`secondStageFeasSet`); for a finite discrete
`ξ` the two agree up to realizations of probability zero, which the book ignores (p. 110). "Finite
discrete" is "almost surely in a finite set". Part (a) takes any `W`, as the book's "for a given ξ"
allows `W(ω)`. -/
theorem theorem_1 {Ω : Type*} [MeasurableSpace Ω] {n1 m1 n2 m2 : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (pb : RecourseData Ω n1 m1 n2 m2) :
    (∀ (W : Matrix (Fin m2) (Fin n2) ℝ) (h : Fin m2 → ℝ) (T : Matrix (Fin m2) (Fin n1) ℝ),
        IsPolyhedralSet (elementaryFeasSet W h T)) ∧
      ((∃ S : Set ((Fin n2 → ℝ) × (Fin m2 → ℝ) × Matrix (Fin m2) (Fin n1) ℝ), S.Finite ∧
          ∀ᵐ ω ∂P, (pb.q ω, pb.h ω, pb.T ω) ∈ S) →
        IsPolyhedralSet (secondStageFeasSet P pb)) := by sorry

end StochasticProg.RecourseKKT
