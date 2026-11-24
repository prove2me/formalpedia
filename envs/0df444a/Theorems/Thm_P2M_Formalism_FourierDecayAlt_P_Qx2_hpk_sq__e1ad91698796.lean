-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Qx2_hpk_sq__e1ad91698796
-- name    : P2M_Formalism_FourierDecayAlt_P_Qx2_hpk_sq__e1ad91698796
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T15:09:36.821171+00:00
-- url     : https://prove2.me/theorems/9af82733-1b86-445b-be97-2f201be6eb9b
-- title:
--   P2 M Formalism Fourier Decay Alt P Qx2 hpk sq  e1ad91698796: P2 M Formalism Fourier Decay Alt P Qx2 hpk sq  e1ad91698796
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Qx2 hpk sq  e1ad91698796 construction uses the P2 M Formalism Fourier Decay Alt P Qx2 hpk sq  e1ad91698796 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumDualVectorEqZeta.lean#L54-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumDualVectorEqZeta.lean#L54-L93

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FinalWR
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.Qx2
variable {k r : ℕ}

theorem P2M_Formalism_FourierDecayAlt_P_Qx2_hpk_sq__e1ad91698796 : Hpk k r * Hpk k r = 1 := by sorry

alias «Formalism».«FourierDecayAlt».«P».«Qx2».«hpk_sq'» := P2M_Formalism_FourierDecayAlt_P_Qx2_hpk_sq__e1ad91698796
