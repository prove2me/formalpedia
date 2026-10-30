-- Prove2me | Theorems.Thm_StochasticProg_RecourseKKT_theorem_2
-- name    : StochasticProg.RecourseKKT.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:50:31.545845+00:00
-- url     : https://prove2.me/theorems/b8823954-f173-409c-8e02-74c8f03b7333
-- title:
--   Theorem 2 — the second-stage value function is piecewise linear, convex in $(h,T)$ and $x$, concave in $q$
-- statement:
--   Let $Q(x,\xi) = \min\{q^{\mathsf T}y \mid Wy = h - Tx,\ y \ge 0\}$ be the second-stage value, with values in $[-\infty, +\infty]$.
--
--   1. For fixed $W$, $q$, $x$: on the set of $(h, T)$ where $Q$ is finite, $(h,T) \mapsto Q(x,\xi)$ is a piecewise linear convex function (and that set is convex).
--   2. For fixed $W$, $h$, $T$, $x$: on the set of $q$ where $Q$ is finite, $q \mapsto Q(x,\xi)$ is a piecewise linear concave function (and that set is convex).
--   3. For fixed $W$, $q$, $h$, $T$: on the set of $x$ where $Q$ is finite, $x \mapsto Q(x,\xi)$ is a piecewise linear convex function (and that set is convex).
--   4. If $\xi$ is a finite discrete random variable and $Q(x,\xi) \ne -\infty$ almost surely for every $x$, then $\mathcal Q$ is finite on $K_2 = \{x \mid \mathcal Q(x) < \infty\}$, and
--   $$
--   \mathcal Q \text{ is piecewise linear and convex on } K_2 .
--   $$
--
--   Part 3 is the convexity of the recourse cost in the first-stage decision on which the expected recourse function's convexity (Theorem 6(a)) and the algorithms of Chapter 5 rest.
--
--   **Formalization Note** Convexity of an extended-valued function with values in $(-\infty, +\infty]$ is convexity of its domain together with convexity there; the Lean statement asks convexity on the set where the value is finite (that set's convexity is part of `ConvexOn`), and evaluates the function as a real number only there.
--
--   Differences from the source:
--   - generalization: (a)–(c) for a given ξ under the standing finiteness of Q (p. 106: unboundedness 'can easily be avoided', x ∈ K₂) → (a)–(c) with no hypothesis, on the set where Q is finite; reason: under the book's finiteness that set is the book's domain ({(h,T) | Q < ∞}, {q | Q > −∞}, K₂(ξ)); without it the statement still holds
--   - generalization: (c) for all x ∈ K₂ → (c) on {x | Q(x, ξ) finite}, which is K₂(ξ) ⊇ K₂ when Q > −∞; reason: K₂ ⊆ K₂(ξ), so the statement on the larger set specializes to the book's
--   - reading: piecewise linear and convex/concave function (extended-valued) → convex domain, convex/concave and piecewise linear (IsPiecewiseLinearOn, affine pieces) on the finite-value set; reason: for functions with values in (−∞, +∞] convexity is convexity of the domain plus convexity on it; the book's pieces q_Bᵀ B⁻¹ (h − Tx) are affine
--   - reading: (d) finite discrete ξ, 𝒬 on K₂, with K₂ = ⋂_{ξ∈Ξ} K₂(ξ) (p. 106) → (d) ξ almost surely in a finite set, Q ≠ −∞ a.s. for every x, on K₂ = {𝒬 < ∞}, with 𝒬 finite there; reason: the §3.1b setting assumes Q finite on K₂ ('for x ∈ K₂, Q(x, ξ) is finite for all ξ', p. 106); the a.s. form is implied by it
--   - encoding: 𝒬(x) = E_ξ Q(x, ξ) with +∞ + (−∞) = +∞ and 0·∞ = 0 → EReal value: +∞ if ∫⁻ Q⁺ = ∞, else ∫⁻ Q⁺ − ∫⁻ Q⁻; reason: the book's convention written out; same instances
-- source:
--   Birge & Louveaux, Introduction to Stochastic Programming, 2nd ed., Springer 2011, doi:10.1007/978-1-4614-0237-4, Chapter 3, §3.1b, Theorem 2, printed p. 107 (PDF p. 132)

import Mathlib
import Definitions.Def_StochasticProg_RecourseKKT_RecourseData
import Definitions.Def_StochasticProg_RecourseKKT_secondStageValue
import Definitions.Def_StochasticProg_RecourseKKT_expectedRecourse
import Definitions.Def_StochasticProg_RecourseKKT_secondStageFeasSet
import Definitions.Def_StochasticProg_RecourseKKT_RecourseNotNegInf
import Definitions.Def_StochasticProg_RecourseKKT_IsPiecewiseLinearOn
open MeasureTheory

namespace StochasticProg.RecourseKKT

/-- **Theorem 2 (piecewise linearity and convexity of the second-stage value function).**
Birge & Louveaux, *Introduction to Stochastic Programming*, 2nd ed., Springer 2011,
doi:10.1007/978-1-4614-0237-4, Chapter 3, §3.1b, Theorem 2, printed p. 107 (PDF p. 132):
"For a given ξ, the value function Q(x, ξ) is
(a) a piecewise linear convex function in (h, T);
(b) a piecewise linear concave function in q;
(c) a piecewise linear convex function in x for all x ∈ K₂.
When ξ is a finite discrete random variable, 𝒬(x) is piecewise linear and convex on K₂."

Clauses (a)–(c) are stated on the set where `Q` is finite (`−∞ < Q < +∞`), with no hypothesis:
(a) for fixed `W, q, x`: on `{(h, T) | Q finite}`, `Q` is convex and piecewise linear;
(b) for fixed `W, h, T, x`: on `{q | Q finite}`, `Q` is concave and piecewise linear;
(c) for fixed `W, q, h, T`: on `{x | Q finite}`, `Q` is convex and piecewise linear;
(d) for a finite discrete `ξ` with `Q(x, ξ) ≠ −∞` (the standing assumption, p. 112): `𝒬` is finite,
convex and piecewise linear on `K₂ = {x | 𝒬(x) < ∞}`.

**Formalization Note.** Under the book's standing finiteness ("Unboundedness … can easily be
avoided", p. 106; "for x ∈ K₂, Q(x, ξ) is finite for all ξ", p. 106) the set where `Q` is finite is
`{Q < ∞}`, the domain of the extended-valued function, and in (c) it is `K₂(ξ) ⊇ K₂`. An
extended-real function with values in `(−∞, +∞]` is convex iff its domain is convex and it is convex
there; `ConvexOn ℝ D f` includes the convexity of `D` (dually `ConcaveOn`). `toReal` is applied only
on the set where the value is finite. -/
theorem theorem_2 {Ω : Type*} [MeasurableSpace Ω] {n1 m1 n2 m2 : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (pb : RecourseData Ω n1 m1 n2 m2) :
    -- (a) piecewise linear convex in (h, T)
    (∀ (W : Matrix (Fin m2) (Fin n2) ℝ) (q : Fin n2 → ℝ) (x : Fin n1 → ℝ),
        ConvexOn ℝ {p : (Fin m2 → ℝ) × Matrix (Fin m2) (Fin n1) ℝ |
            ⊥ < secondStageValue W q p.1 p.2 x ∧ secondStageValue W q p.1 p.2 x < ⊤}
          (fun p => (secondStageValue W q p.1 p.2 x).toReal) ∧
        IsPiecewiseLinearOn (fun p : (Fin m2 → ℝ) × Matrix (Fin m2) (Fin n1) ℝ =>
            (secondStageValue W q p.1 p.2 x).toReal)
          {p : (Fin m2 → ℝ) × Matrix (Fin m2) (Fin n1) ℝ |
            ⊥ < secondStageValue W q p.1 p.2 x ∧ secondStageValue W q p.1 p.2 x < ⊤}) ∧
    -- (b) piecewise linear concave in q
    (∀ (W : Matrix (Fin m2) (Fin n2) ℝ) (h : Fin m2 → ℝ) (T : Matrix (Fin m2) (Fin n1) ℝ)
        (x : Fin n1 → ℝ),
        ConcaveOn ℝ {q : Fin n2 → ℝ |
            ⊥ < secondStageValue W q h T x ∧ secondStageValue W q h T x < ⊤}
          (fun q => (secondStageValue W q h T x).toReal) ∧
        IsPiecewiseLinearOn (fun q : Fin n2 → ℝ => (secondStageValue W q h T x).toReal)
          {q : Fin n2 → ℝ | ⊥ < secondStageValue W q h T x ∧ secondStageValue W q h T x < ⊤}) ∧
    -- (c) piecewise linear convex in x
    (∀ (W : Matrix (Fin m2) (Fin n2) ℝ) (q : Fin n2 → ℝ) (h : Fin m2 → ℝ)
        (T : Matrix (Fin m2) (Fin n1) ℝ),
        ConvexOn ℝ {x : Fin n1 → ℝ |
            ⊥ < secondStageValue W q h T x ∧ secondStageValue W q h T x < ⊤}
          (fun x => (secondStageValue W q h T x).toReal) ∧
        IsPiecewiseLinearOn (fun x : Fin n1 → ℝ => (secondStageValue W q h T x).toReal)
          {x : Fin n1 → ℝ | ⊥ < secondStageValue W q h T x ∧ secondStageValue W q h T x < ⊤}) ∧
    -- (d) finite discrete ξ: 𝒬 piecewise linear and convex on K₂
    ((∃ S : Set ((Fin n2 → ℝ) × (Fin m2 → ℝ) × Matrix (Fin m2) (Fin n1) ℝ), S.Finite ∧
          ∀ᵐ ω ∂P, (pb.q ω, pb.h ω, pb.T ω) ∈ S) →
      RecourseNotNegInf P pb →
        (∀ x ∈ secondStageFeasSet P pb, expectedRecourse P pb x ≠ ⊥) ∧
        ConvexOn ℝ (secondStageFeasSet P pb) (fun x => (expectedRecourse P pb x).toReal) ∧
        IsPiecewiseLinearOn (fun x => (expectedRecourse P pb x).toReal)
          (secondStageFeasSet P pb)) := by sorry

end StochasticProg.RecourseKKT
