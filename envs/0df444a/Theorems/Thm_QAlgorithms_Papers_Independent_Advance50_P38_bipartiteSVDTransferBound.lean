-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P38_bipartiteSVDTransferBound
-- name    : QAlgorithms.Papers.Independent.Advance50.P38.bipartiteSVDTransferBound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:45:53.798067+00:00
-- url     : https://prove2.me/theorems/7282f11d-b36a-426e-9629-8ccc1f84a86e
-- title:
--   Proposition IV.1: bipartite SVD transfer bound
-- statement:
--   Let $N_1,N_2>0$ and let $X,Y\in\mathbb C^{N_1\times N_2}$ have full singular-value decompositions $X=V_X\Sigma_XW_X^\dagger$ and $Y=V_Y\Sigma_YW_Y^\dagger$, with unitary factors and nonnegative singular values sorted decreasingly. Let $x=\operatorname{vec}X,y=\operatorname{vec}Y$ use column vectorization. The local-transfer maximum is attained and satisfies
--   $$\max_{U\in\mathrm{SU}(N_2)\otimes\mathrm{SU}(N_1)}\operatorname{Re}\operatorname{tr}(xx^\dagger Uyy^\dagger U^\dagger)\le\bigl(\operatorname{tr}(\Sigma_X^\dagger\Sigma_Y)\bigr)^2.$$
--   If all four SVD factors have determinant one, equality is achieved by $U_*=(\overline{W_X}\otimes V_X)(W_Y^\top\otimes V_Y^\dagger)$, which lies in the required local subgroup. This determinant condition is sufficient. The matrices need not be normalized.
-- source:
--   Gradient Flows for Optimisation and Quantum Control: Foundations and Applications, arXiv:0802.4195v2, PDF p. 27, Proposition IV.1: bipartite SVD transfer bound

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P38

namespace QAlgorithms.Papers.Independent.Advance50.P38

open scoped BigOperators Topology Manifold ContDiff

noncomputable section

/-- Proposition IV.1, PDF p.27: attained maximum, rectangular SVD bound,
and the source's sufficient determinant-one equality case. -/
theorem bipartiteSVDTransferBound {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (X Y : Matrix (Fin a) (Fin b) ℂ) (sx : FullSVD X) (sy : FullSVD Y) :
    let values : Set ℝ := {r | ∃ V : Matrix.specialUnitaryGroup (Fin a) ℂ,
      ∃ W : Matrix.specialUnitaryGroup (Fin b) ℂ,
        r = pureStateTransfer (colVec X) (colVec Y) (Matrix.kronecker (W : (Matrix (Fin b) (Fin b) ℂ)) (V : (Matrix (Fin a) (Fin a) ℂ)))}
    let bound := (Matrix.trace ((rectangularSigma (a := a) (b := b) sx.singularValues).conjTranspose *
      rectangularSigma (a := a) (b := b) sy.singularValues)).re ^ 2
    (∃ r, IsGreatest values r ∧ r ≤ bound) ∧
    ((sx.V : (Matrix (Fin a) (Fin a) ℂ)).det = 1 → (sy.V : (Matrix (Fin a) (Fin a) ℂ)).det = 1 →
      (sx.W : (Matrix (Fin b) (Fin b) ℂ)).det = 1 → (sy.W : (Matrix (Fin b) (Fin b) ℂ)).det = 1 →
      (∃ V : Matrix.specialUnitaryGroup (Fin a) ℂ,
        ∃ W : Matrix.specialUnitaryGroup (Fin b) ℂ,
          svdOptimizer sx sy = Matrix.kronecker (W : (Matrix (Fin b) (Fin b) ℂ)) (V : (Matrix (Fin a) (Fin a) ℂ))) ∧
      pureStateTransfer (colVec X) (colVec Y) (svdOptimizer sx sy) = bound) := by sorry

end

end QAlgorithms.Papers.Independent.Advance50.P38
