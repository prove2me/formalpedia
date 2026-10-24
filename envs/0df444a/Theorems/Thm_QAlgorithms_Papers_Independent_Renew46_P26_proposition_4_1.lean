-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P26_proposition_4_1
-- name    : QAlgorithms.Papers.Independent.Renew46.P26.proposition_4_1
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T20:54:47.219926+00:00
-- url     : https://prove2.me/theorems/ac7939f7-8dc4-4827-bbf5-484dc46e1f2f
-- title:
--   Proposition 4.1
-- statement:
--   Let $\alpha=(a_1,\ldots,a_n)$ be an actual joint YJM weight in a nonzero irreducible complex $S_n$-module, with nonzero eigenvector $v$. All $a_j$ are integers and $a_i\ne a_{i+1}$. If $a_{i+1}=a_i\pm1$, then $s_iv=\pm v$. Otherwise set $r=a_{i+1}-a_i$, $\beta=s_i\alpha$ and $w=(s_i-r^{-1})v$. Then $\beta\in\operatorname{Spec}(n)$ and $\beta\sim\alpha$, the vectors $v,w$ are linearly independent, and $w$ has weight $\beta$. In their span,
--
--   $$s_iv=r^{-1}v+w,\qquad s_iw=(1-r^{-2})v-r^{-1}w.$$
--
--   The $X_i,X_{i+1}$ actions are diagonal with eigenvalues $(a_i,a_{i+1})$ on $v$ and the reversed values on $w$. The definition of $w$ fixes its local scaling without constraining other basis phases.
-- source:
--   A New Approach to the Representation Thoery of the Symmetric Groups. 2, arXiv:math/0503040v3, PDF p. 16, Proposition 4.1

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P26

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P26

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- Proposition 4.1 (PDF pp.16–17). All integer and adjacent-weight clauses
are retained. The new vector is scaled locally by (s_i-1/r)v; this is not a
simultaneous constraint on previously chosen phases of every basis vector. -/
theorem proposition_4_1 {n d : ℕ}
    (rho : SymmetricAlgebra n →ₐ[ℂ] Module.End ℂ (Fin d → ℂ))
    (hrho : IsIrreducibleAlgebra rho) (alpha : Fin n → ℂ) (v : Fin d → ℂ)
    (hv : IsWeightVector rho alpha v) :
    (∀ j : Fin n, ∃ z : ℤ, alpha j = (z : ℂ)) ∧
    (∀ i : Adjacent n, alpha i.val ≠ alpha (nextPosition i)) ∧
    (∀ i : Adjacent n,
      (alpha (nextPosition i) = alpha i.val + 1 → rho (adjacentElement i) v = v) ∧
      (alpha (nextPosition i) = alpha i.val - 1 → rho (adjacentElement i) v = -v)) ∧
    (∀ i : Adjacent n, alpha (nextPosition i) ≠ alpha i.val + 1 →
      alpha (nextPosition i) ≠ alpha i.val - 1 →
      let beta := alpha ∘ adjacentPerm i
      let r := alpha (nextPosition i) - alpha i.val
      let w := rho (adjacentElement i) v - r⁻¹ • v
      beta ∈ spectrum n ∧ SameIrreducible alpha beta ∧
      IsWeightVector rho beta w ∧ LinearIndependent ℂ ![v, w] ∧
      rho (adjacentElement i) v = r⁻¹ • v + w ∧
      rho (adjacentElement i) w = (1 - (r⁻¹)^2) • v - r⁻¹ • w) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P26

end
