-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P15_highestWeight_canonical_basis
-- name    : QAlgorithms.Papers.Independent.Renew46.P15.highestWeight_canonical_basis
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T20:16:14.016208+00:00
-- url     : https://prove2.me/theorems/0706a186-afcd-4b5c-b266-a69f954cf32d
-- title:
--   Canonical orthonormal highest-weight CG basis
-- statement:
--   Fix an integer $N\ge2$ and two arbitrary finite-dimensional irreducible representations $S,S^\prime$ of $\mathrm{SU}(N)$, with normalized weakly decreasing integral top rows ending in zero. Use their orthonormal Gelfand–Tsetlin (GT) bases, without normalizing lower rows, and the real CG coefficients intertwining the common complexified Lie-algebra generators. These same coefficients apply to $\mathrm{SL}(N,\mathbb C)$.
--
--   Fix an occurring output irrep $T$ and a column order on the product basis. Insert zero columns outside the highest-weight selection space, and let $A$ be any matrix whose rows form a full independent family spanning the highest-weight solution space $K_T$. There is a unique reduced row echelon matrix $R$ with the same row space and with unit leading pivots. Apply normalized Gram–Schmidt to its rows in their increasing row order. Writing the resulting rows as $u_i$, one obtains
--
--   $$
--    \langle u_i,u_j\rangle=\delta_{ij},\qquad
--    \operatorname{span}\{u_i\}=K_T.
--   $$
--
--   Every pre-normalization residual is nonzero. The resulting ordered orthonormal highest-weight coefficient family is uniquely determined by the fixed column order, independently of the initial full solution family. This fixes phases and multiplicity bases by the convention of §X; it does not assert that the default numerical implementation enables this convention.
-- source:
--   A numerical algorithm for the explicit calculation of SU(N) and SL(N,C) Clebsch-Gordan coefficients, arXiv:1009.0437v2, PDF p. 12, §X, Eq.(37)

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P15

noncomputable section

open scoped BigOperators Matrix

namespace QAlgorithms.Papers.Independent.Renew46.P15

attribute [local instance] Classical.propDecidable

/-- X, (37), PDF p.12: at any fixed column order, RREF then normalized
Gram-Schmidt specifies a unique orthonormal highest-weight basis. The input
rows are any full independent family of solutions. Unit pivots fix the printed
positive row-scaling freedom before the final normalization. -/
theorem highestWeight_canonical_basis {n r m : ℕ} (s sPrime : GTTopRow n)
    (t : Fin r → GTTopRow n) (c : CGTable s sPrime t) (j : Fin r)
    (order : Fin (Fintype.card (Pattern s × Pattern sPrime)) ≃
      (Pattern s × Pattern sPrime))
    (a : Matrix (Fin m) (Fin (Fintype.card (Pattern s × Pattern sPrime))) ℝ)
    (independent : LinearIndependent ℝ (fun i p => a i (order.symm p)))
    (complete : Submodule.span ℝ (Set.range (fun i p => a i (order.symm p))) =
      highestKernel s sPrime (t j)) :
    ∃! b : Matrix (Fin m) (Fin (Fintype.card (Pattern s × Pattern sPrime))) ℝ,
      IsRREF b ∧
      Submodule.span ℝ (Set.range (euclideanRow b)) =
        Submodule.span ℝ (Set.range (euclideanRow a)) ∧
      Orthonormal ℝ (canonicalRows b) ∧
      Submodule.span ℝ (Set.range (canonicalRows b)) =
        Submodule.span ℝ (Set.range (euclideanRow a)) ∧
      ∀ i, InnerProductSpace.gramSchmidt ℝ (euclideanRow b) i ≠ 0 := by sorry

end QAlgorithms.Papers.Independent.Renew46.P15

end
