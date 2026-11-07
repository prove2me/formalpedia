-- Prove2me | Theorems.Thm_PathCount2k_lemma_2_13
-- name    : PathCount2k.lemma_2_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:46:28.460814+00:00
-- url     : https://prove2.me/theorems/b1e1b000-6ee0-4a6d-a542-3db801804107
-- title:
--   Lemma 2.13 — moment matching for polynomials of individual degree $\le4$
-- statement:
--   Let $F(x_1,\dots,x_s)$ be a real polynomial whose degree in each individual variable is at most four. Let $X_1,\dots,X_s$ be independent standard Gaussian variables and $\xi_1,\dots,\xi_s$ independent copies of $\xi$ (Definition 2.15). Then
--   $$
--   \mathbb E\big[F(X_1,\dots,X_s)\big]=\mathbb E\big[F(\xi_1,\dots,\xi_s)\big].
--   $$
--
--   The degree condition is per variable; the total degree may exceed four. This lets the finite law replace the Gaussian one in the second and fourth moments of $Z$.
--
--   Differences from the source:
--
--   - encoding: a real polynomial in x₁, …, x_s with degree ≤ 4 in each variable → F : MvPolynomial (Fin s) ℝ with F.degreeOf i ≤ 4 for every i; expectations as integrals against Measure.pi; reason: same objects
--   - encoding: the expectation E[F(X₁, …, X_s)] and E[F(ξ₁, …, ξ_s)] → Integrable … ∧ the Bochner integral bound; reason: Lean's integral is 0 on a non-integrable function; the paper's expectation exists, so stating integrability excludes only the junk case
-- source:
--   Panolan, Saurabh, Xue, Zehavi, Counting Paths in Time O*(2^k), with Extensions to Counting Bounded Treewidth Graphs and Multilinear Monomials, STOC 2027 submission manuscript (Nov 2026), Lemma 2.13, p.13 (with Observation 2.6)

import Mathlib
import Definitions.Def_PathCount2k_Graph
import Definitions.Def_PathCount2k_Exterior
import Definitions.Def_PathCount2k_Gaussian
import Definitions.Def_PathCount2k_Finite

open MeasureTheory ProbabilityTheory

namespace PathCount2k

/-- Panolan, Saurabh, Xue, Zehavi, *Counting Paths in Time O\*(2^k), with Extensions to Counting
Bounded Treewidth Graphs and Multilinear Monomials*, STOC 2027 submission manuscript (Nov 2026), **Lemma 2.13** (Moment matching for polynomials), p.13: "Let `F(x₁, …, x_s)` be a
real polynomial whose degree in each individual variable is at most four. Let `X₁, …, X_s` be
independent standard Gaussian variables, and let `ξ₁, …, ξ_s` be independent copies of `ξ`. Then
`E[F(X₁, …, X_s)] = E[F(ξ₁, …, ξ_s)]`."

**Formalization Note.** The degree condition is per variable (`MvPolynomial.degreeOf`), not on
the total degree ("The degree condition is per variable; the total degree may exceed four",
p.13). `ξ` has the law `xiLaw` of Definition 2.15. The integrability of `F` under both laws
is stated too. -/
theorem lemma_2_13 (s : ℕ) (F : MvPolynomial (Fin s) ℝ) (hF : ∀ i, F.degreeOf i ≤ 4) :
    Integrable (fun x => MvPolynomial.eval x F) (Measure.pi fun _ : Fin s => gaussianReal 0 1) ∧
      Integrable (fun x => MvPolynomial.eval x F) (Measure.pi fun _ : Fin s => xiLaw) ∧
      ∫ x, MvPolynomial.eval x F ∂(Measure.pi fun _ : Fin s => gaussianReal 0 1) =
        ∫ x, MvPolynomial.eval x F ∂(Measure.pi fun _ : Fin s => xiLaw) := by sorry

end PathCount2k
