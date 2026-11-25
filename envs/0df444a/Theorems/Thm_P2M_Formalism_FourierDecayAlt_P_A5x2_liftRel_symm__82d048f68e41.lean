-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_A5x2_liftRel_symm__82d048f68e41
-- name    : P2M_Formalism_FourierDecayAlt_P_A5x2_liftRel_symm__82d048f68e41
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:54:55.473944+00:00
-- url     : https://prove2.me/theorems/e3f1b127-9cd5-4e42-b94d-3f58222ef671
-- title:
--   P2 M Formalism Fourier Decay Alt P A5x2 lift Rel symm  82d048f68e41: P2 M Formalism Fourier Decay Alt P A5x2 lift Rel symm  82d048f68e41
-- statement:
--   The P2 M Formalism Fourier Decay Alt P A5x2 lift Rel symm  82d048f68e41 construction uses the P2 M Formalism Fourier Decay Alt P A5x2 lift Rel symm  82d048f68e41 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ColumnOperationTripleForm.lean#L243-L245
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ColumnOperationTripleForm.lean#L243-L245

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x2
open Formalism.DoubleCosetMeasures.P Formalism.DoubleCosetMeasures.P.Phase
variable {K : Type} [CommRing K] (R : Subring K) {n : ℕ}
variable {R}

theorem P2M_Formalism_FourierDecayAlt_P_A5x2_liftRel_symm__82d048f68e41 {k : ℕ} {Z Z' : Matrix (Fin n) (Fin n) K} {φ : coker R Z ≃ₗ[R] coker R Z'}
    {v v' : Fin n → R} (h : LiftRel R k Z' Z φ.symm v' v) : LiftRel R k Z Z' φ v v' := by sorry

alias «Formalism».«FourierDecayAlt».«P».«A5x2».«liftRel_symm'» := P2M_Formalism_FourierDecayAlt_P_A5x2_liftRel_symm__82d048f68e41
