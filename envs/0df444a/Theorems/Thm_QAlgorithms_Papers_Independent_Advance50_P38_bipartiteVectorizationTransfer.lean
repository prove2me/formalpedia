-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P38_bipartiteVectorizationTransfer
-- name    : QAlgorithms.Papers.Independent.Advance50.P38.bipartiteVectorizationTransfer
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T08:52:10.652739+00:00
-- url     : https://prove2.me/theorems/5b28878c-9160-405c-b790-c6b00bf74235
-- title:
--   §IV.B: vectorization and transfer identities (172)
-- statement:
--   Let $N_1,N_2>0$, let $X,Y\in\mathbb C^{N_1\times N_2}$, and let $V\in\mathrm U(N_1),W\in\mathrm U(N_2)$. For column vectorization and the usual conjugate-linear-first inner product,
--   $$\operatorname{vec}(VYW)=(W^\top\otimes V)\operatorname{vec}Y,\qquad\langle\operatorname{vec}X,\operatorname{vec}Y\rangle=\operatorname{tr}(X^\dagger Y).$$
--   Putting $x=\operatorname{vec}X,y=\operatorname{vec}Y$ and $U=W\otimes V$ gives $\operatorname{tr}(xx^\dagger Uyy^\dagger U^\dagger)=|\langle x,\operatorname{vec}(VYW^\top)\rangle|^2=|\operatorname{tr}(X^\dagger VYW^\top)|^2$. In particular this trace is real and equals the transfer objective.
-- source:
--   Gradient Flows for Optimisation and Quantum Control: Foundations and Applications, arXiv:0802.4195v2, PDF p. 27, §IV.B: vectorization and transfer identities (172)

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P38

namespace QAlgorithms.Papers.Independent.Advance50.P38

open scoped BigOperators Topology Manifold ContDiff

noncomputable section

/-- Vectorization and pureStateTransfer (172), PDF p.27: column order, ordinary
transpose on W, and a modulus-square trace. -/
theorem bipartiteVectorizationTransfer {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (X Y : Matrix (Fin a) (Fin b) ℂ)
    (V : Matrix.unitaryGroup (Fin a) ℂ) (W : Matrix.unitaryGroup (Fin b) ℂ) :
    colVec ((V : (Matrix (Fin a) (Fin a) ℂ)) * Y * (W : (Matrix (Fin b) (Fin b) ℂ))) =
      (Matrix.kronecker (W : (Matrix (Fin b) (Fin b) ℂ)).transpose (V : (Matrix (Fin a) (Fin a) ℂ))).mulVec (colVec Y) ∧
    vInner (colVec X) (colVec Y) = Matrix.trace (X.conjTranspose * Y) ∧
    Matrix.trace (rankOneMatrix (colVec X) * Matrix.kronecker (W : (Matrix (Fin b) (Fin b) ℂ)) (V : (Matrix (Fin a) (Fin a) ℂ)) *
      rankOneMatrix (colVec Y) * (Matrix.kronecker (W : (Matrix (Fin b) (Fin b) ℂ)) (V : (Matrix (Fin a) (Fin a) ℂ))).conjTranspose) =
      (Complex.normSq (Matrix.trace (X.conjTranspose * (V : (Matrix (Fin a) (Fin a) ℂ)) * Y * (W : (Matrix (Fin b) (Fin b) ℂ)).transpose)) : ℂ) ∧
    pureStateTransfer (colVec X) (colVec Y) (Matrix.kronecker (W : (Matrix (Fin b) (Fin b) ℂ)) (V : (Matrix (Fin a) (Fin a) ℂ))) =
      Complex.normSq (vInner (colVec X) (colVec ((V : (Matrix (Fin a) (Fin a) ℂ)) * Y * (W : (Matrix (Fin b) (Fin b) ℂ)).transpose))) := by sorry

end

end QAlgorithms.Papers.Independent.Advance50.P38
