-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P38_cSpectralNormTransferBound
-- name    : QAlgorithms.Papers.Independent.Advance50.P38.cSpectralNormTransferBound
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T08:46:30.464632+00:00
-- url     : https://prove2.me/theorems/721fa32e-e7fd-456e-afb9-dfe7c063e4f3
-- title:
--   Corollary IV.1: squared C-spectral-norm bound
-- statement:
--   For $N_1,N_2>0$ and $A,C\in\mathbb C^{N_1\times N_2}$, write $x=\operatorname{vec}A,y=\operatorname{vec}C$ in column order and define
--   $$\|A\|_C^2=\max_{V\in\mathrm U(N_1),\,W\in\mathrm U(N_2)}|\operatorname{tr}(C^\dagger VAW^\dagger)|^2.$$
--   Both this real-valued maximum and the local special-unitary transfer maximum are attained. The latter is at most $\|A\|_C^2$. The modulus and square are essential; no maximum of complex numbers is used.
-- source:
--   Gradient Flows for Optimisation and Quantum Control: Foundations and Applications, arXiv:0802.4195v2, PDF p. 27, Corollary IV.1: squared C-spectral-norm bound

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P38

namespace QAlgorithms.Papers.Independent.Advance50.P38

open scoped BigOperators Topology Manifold ContDiff

noncomputable section

/-- Corollary IV.1, PDF p.27: the real modulus-square maximum bounds
local transfer. Attainment guards the real supremum definition. -/
theorem cSpectralNormTransferBound {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (A C : Matrix (Fin a) (Fin b) ℂ) :
    IsGreatest {r | ∃ V : Matrix.unitaryGroup (Fin a) ℂ,
      ∃ W : Matrix.unitaryGroup (Fin b) ℂ,
        r = Complex.normSq (Matrix.trace (C.conjTranspose * (V : (Matrix (Fin a) (Fin a) ℂ)) * A *
          (W : (Matrix (Fin b) (Fin b) ℂ)).conjTranspose))} (cSpectralSq A C) ∧
    ∃ r, IsGreatest {r | ∃ V : Matrix.specialUnitaryGroup (Fin a) ℂ,
      ∃ W : Matrix.specialUnitaryGroup (Fin b) ℂ,
        r = pureStateTransfer (colVec A) (colVec C) (Matrix.kronecker (W : (Matrix (Fin b) (Fin b) ℂ)) (V : (Matrix (Fin a) (Fin a) ℂ)))} r ∧
      r ≤ cSpectralSq A C := by sorry

end

end QAlgorithms.Papers.Independent.Advance50.P38
