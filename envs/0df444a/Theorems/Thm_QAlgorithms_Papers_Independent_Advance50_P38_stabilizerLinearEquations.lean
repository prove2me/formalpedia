-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P38_stabilizerLinearEquations
-- name    : QAlgorithms.Papers.Independent.Advance50.P38.stabilizerLinearEquations
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T08:53:36.41525+00:00
-- url     : https://prove2.me/theorems/9ee2d47c-3a51-4e78-9547-3ed10194e9f4
-- title:
--   §IV.D: centralizer linear equations (199)
-- statement:
--   Let $N>0$ and $E\in\mathbb C^{N\times N}$. Define $\mathfrak k_E=\{K:K^\dagger=-K,\,[K,E]=0\}\subseteq\mathfrak u(N)$. In column vectorization order,
--   $$\mathfrak k_E=\{K\in\mathfrak u(N):(I\otimes E-E^\top\otimes I)\operatorname{vec}K=0\}.$$
--   This real vector space is closed under commutators. If $E=\mu I+\Omega$ with $\mu\in\mathbb C$ and $\Omega\in\mathfrak u(N)$, then $\mathfrak k_E=\mathfrak k_\Omega$. No trace-zero restriction is imposed.
-- source:
--   Gradient Flows for Optimisation and Quantum Control: Foundations and Applications, arXiv:0802.4195v2, PDF p. 32, §IV.D: centralizer linear equations (199)

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P38

namespace QAlgorithms.Papers.Independent.Advance50.P38

open scoped BigOperators Topology Manifold ContDiff

noncomputable section

/-- Centralizer equations (199), PDF p.32, Lie closure and scalar-shift case. -/
theorem stabilizerLinearEquations {n : ℕ} (hn : 0 < n) (E : (Matrix (Fin n) (Fin n) ℂ)) :
    centralizerAlgebra E = {K : (Matrix (Fin n) (Fin n) ℂ) | K.conjTranspose = -K ∧
      (centralizerMatrix E).mulVec (colVec K) = 0} ∧
    (∀ K L : (Matrix (Fin n) (Fin n) ℂ), K ∈ centralizerAlgebra E → L ∈ centralizerAlgebra E →
      comm K L ∈ centralizerAlgebra E) ∧
    ∀ (mu : ℂ) (Omega : (Matrix (Fin n) (Fin n) ℂ)), Omega.conjTranspose = -Omega →
      E = mu • (1 : (Matrix (Fin n) (Fin n) ℂ)) + Omega → centralizerAlgebra E = centralizerAlgebra Omega := by sorry

end

end QAlgorithms.Papers.Independent.Advance50.P38
