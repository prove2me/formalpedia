-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P22_semisimple_hull_characters
-- name    : QAlgorithms.Papers.Independent.Renew46.P22.semisimple_hull_characters
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T20:32:32.643825+00:00
-- url     : https://prove2.me/theorems/f3e1dce0-73ca-45e6-ac70-fed61a1055b8
-- title:
--   Chevalley: integer eigenvalue characters define the semisimple group hull
-- statement:
--   Let F have characteristic zero, let K be its specified algebraic closure, and let X in Mₙ(F) be semisimple. Suppose A in GLₙ(K) satisfies A X A⁻¹=Y=diag(α₁,…,αₙ), with X mapped into K. Define Λ={e in ℤⁿ : ∑ᵢeᵢαᵢ=0}. Then G(Y) consists exactly of the invertible diagonal matrices diag(c₁,…,cₙ) such that ∏ᵢcᵢ^{eᵢ}=1 for every e in Λ. Moreover G(X)=A⁻¹G(Y)A. Both hulls are intrinsic intersections of algebraic tangent-containing subgroups.
-- source:
--   Constructing algebraic groups from their Lie algebras, arXiv:math/0612557v1, PDF p. 5, Theorem 5 (Chevalley)

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P22

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P22

open scoped BigOperators Pointwise

attribute [local instance 100] LieRing.ofAssociativeRing

section Relations

variable {K : Type*} [Field K] [CharZero K] {m n : ℕ}

variable {F : Type*} [Field F] [hcharF : CharZero F] [Algebra F K] [hclosureF : IsAlgClosure F K]

section

include hcharF hclosureF

/-- Theorem 5 (Chevalley), PDF p.5, first clause cited there from [2], Chapter II,
Proposition 2. The hull of the constructed diagonal matrix is cut out by every
integer eigenvalue relation, and the original hull is its conjugate by A inverse.
All points are invertible: nonzero diagonal coordinates make signed powers explicit. -/
theorem semisimple_hull_characters
    (X : Matrix (Fin n) (Fin n) F)
    (hX : Module.End.IsSemisimple (Matrix.mulVecLin X))
    (alpha : Fin n → K) (A : GeometricGL n K)
    (hdiag : (A : Matrix (Fin n) (Fin n) K) *
      (X.map (algebraMap F K)) *
      (A⁻¹ : Matrix (Fin n) (Fin n) K) = Matrix.diagonal alpha) :
    let Y := Matrix.diagonal alpha
    let HY := groupHull K K (Submodule.span K {Y})
    (HY : Set (GeometricGL n K)) =
      {g : GeometricGL n K | ∃ c : Fin n → K, (∀ i, c i ≠ 0) ∧
        (g : Matrix (Fin n) (Fin n) K) = Matrix.diagonal c ∧
        ∀ e ∈ relationKernel ℤ alpha, (∏ i, (c i) ^ (e i)) = 1} ∧
    (groupHull F K (Submodule.span F {X}) : Set (GeometricGL n K)) =
      {g | A * g * A⁻¹ ∈ HY} := by sorry

end

end Relations

end QAlgorithms.Papers.Independent.Renew46.P22

end
