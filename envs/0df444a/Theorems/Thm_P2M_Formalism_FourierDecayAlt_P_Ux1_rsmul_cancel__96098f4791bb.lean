-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Ux1_rsmul_cancel__96098f4791bb
-- name    : P2M_Formalism_FourierDecayAlt_P_Ux1_rsmul_cancel__96098f4791bb
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:56:47.245492+00:00
-- url     : https://prove2.me/theorems/f1a42467-b19e-4d5b-8f89-55a1c729a230
-- title:
--   P2 M Formalism Fourier Decay Alt P Ux1 rsmul cancel  96098f4791bb: P2 M Formalism Fourier Decay Alt P Ux1 rsmul cancel  96098f4791bb
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Ux1 rsmul cancel  96098f4791bb construction uses the P2 M Formalism Fourier Decay Alt P Ux1 rsmul cancel  96098f4791bb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CompactlySupportedBanachModel.lean#L796-L799
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CompactlySupportedBanachModel.lean#L796-L799

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CayleyForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactlySupportedBanachModel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux1
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem P2M_Formalism_FourierDecayAlt_P_Ux1_rsmul_cancel__96098f4791bb {g : Mat k r} (hg : g ∈ GV k r) (a : ℝ) (e : E) :
    ((gN g ^ a : ℝ) : ℂ) • ((gN g ^ (-a) : ℝ) : ℂ) • e = e := by sorry

alias «Formalism».«FourierDecayAlt».«P».«Ux1».«rsmul_cancel'» := P2M_Formalism_FourierDecayAlt_P_Ux1_rsmul_cancel__96098f4791bb
