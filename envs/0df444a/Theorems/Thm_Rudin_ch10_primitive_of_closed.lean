-- Prove2me | Theorems.Thm_Rudin_ch10_primitive_of_closed
-- name    : Rudin.ch10_primitive_of_closed
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T00:18:48.697068+00:00
-- url     : https://prove2.me/theorems/a45d7db0-ed01-4e57-b16d-c55e8e61d1cf
-- title:
--   Poincare's lemma, pointwise form: a closed form on a convex set has a primitive
-- statement:
--   This is the analytic core of Rudin's Theorem 10.39 (Poincare's lemma), stated pointwise rather
--   than through integrals over surfaces.
--
--   Let $E \subseteq \mathbb{R}^n$ be convex and open and let $\omega$ be a $(m+1)$-form of class $C'$
--   in $E$ which is closed in the pointwise sense that its exterior derivative vanishes as an
--   alternating form:
--
--   $$\sum_{\sigma \in S_{m+2}} \operatorname{sgn}(\sigma)\,(d\omega)_{i\circ\sigma}(x) = 0
--   \qquad (x \in E).$$
--
--   Then $\omega$ has a primitive: there is an $m$-form $\eta$ of class $C'$ in $E$ with
--   $d\eta = \omega$, the equality again being understood as an equality of alternating forms, i.e.
--
--   $$\sum_{\sigma \in S_{m+1}} \operatorname{sgn}(\sigma)\,(d\eta)_{i\circ\sigma}(x)
--   = \sum_{\sigma \in S_{m+1}} \operatorname{sgn}(\sigma)\,\omega_{i\circ\sigma}(x)
--   \qquad (x \in E)$$
--
--   for every index tuple $i$. Since a form is presented here by coefficients indexed by all tuples,
--   not only the increasing ones, the alternating sums are the invariant content of the equation
--   $d\eta = \omega$; two forms with the same alternations have the same integrals over all surfaces.
--   The standard construction of $\eta$ on a convex set is the homotopy (cone) operator based at a
--   point of $E$, integrating the coefficients of $\omega$ along the segments joining that point to
--   $x$.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 10, Theorem 10.39 (Poincare's lemma), pp. 275-280

import Mathlib
import Definitions.Def_Rudin_ch10_forms

open Filter Topology MeasureTheory

namespace Rudin

/-- Rudin, Theorem 10.39 (Poincaré's lemma), pointwise form: on a convex open set `E` every
`(m+1)`-form `ω` of class `C'` whose exterior derivative vanishes as an alternating form has a
primitive.  That is, there is an `m`-form `η` of class `C'` in `E` with `dη = ω` as alternating
forms: at every point of `E` the alternating sums of the coefficients of `dη` and of `ω` agree. -/
theorem ch10_primitive_of_closed (m n : ℕ) (E : Set (Fin n → ℝ)) (hE : IsOpen E)
    (hconv : Convex ℝ E) (ω : KForm (m + 1) n) (hω : ∀ i, ContDiffOn ℝ 1 (ω.coeff i) E)
    (hclosed : ∀ x ∈ E, ∀ i : Fin (m + 1 + 1) → Fin n,
      ∑ σ : Equiv.Perm (Fin (m + 1 + 1)), (Equiv.Perm.sign σ : ℝ) *
        (extDeriv ω).coeff (fun r => i (σ r)) x = 0) :
    ∃ η : KForm m n, (∀ i, ContDiffOn ℝ 1 (η.coeff i) E) ∧
      ∀ x ∈ E, ∀ i : Fin (m + 1) → Fin n,
        ∑ σ : Equiv.Perm (Fin (m + 1)), (Equiv.Perm.sign σ : ℝ) *
            (extDeriv η).coeff (fun r => i (σ r)) x
          = ∑ σ : Equiv.Perm (Fin (m + 1)), (Equiv.Perm.sign σ : ℝ) *
            ω.coeff (fun r => i (σ r)) x := by sorry

end Rudin
