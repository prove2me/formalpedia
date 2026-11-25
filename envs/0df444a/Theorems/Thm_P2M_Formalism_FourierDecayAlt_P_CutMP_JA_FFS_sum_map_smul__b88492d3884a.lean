-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_CutMP_JA_FFS_sum_map_smul__b88492d3884a
-- name    : P2M_Formalism_FourierDecayAlt_P_CutMP_JA_FFS_sum_map_smul__b88492d3884a
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T07:53:28.193008+00:00
-- url     : https://prove2.me/theorems/1827ec1c-40bd-5b08-bc6c-bf5b7a59e818
-- title:
--   P2 M Formalism Fourier Decay Alt P Cut MP JA FFS sum map smul  b88492d3884a: P2 M Formalism Fourier Decay Alt P Cut MP JA FFS sum map smul  b88492d3884a
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Cut MP JA FFS sum map smul  b88492d3884a construction uses the P2 M Formalism Fourier Decay Alt P Cut MP JA FFS sum map smul  b88492d3884a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutJAFFStableGerm.lean#L68-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutJAFFStableGerm.lean#L68-L72

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJAFFStable2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJAFFStableGerm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA Formalism.FourierDecayAlt.P.CutMP.JA.FFS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E']

theorem P2M_Formalism_FourierDecayAlt_P_CutMP_JA_FFS_sum_map_smul__b88492d3884a {ι M : Type*} [AddCommMonoid M] [Module ℂ M] (c : ℂ) (l : List ι) (φ : ι → M) :
    (l.map fun i => c • φ i).sum = c • (l.map φ).sum := by sorry

alias «Formalism».«FourierDecayAlt».«P».«CutMP».«JA».«FFS».«sum_map_smul'» := P2M_Formalism_FourierDecayAlt_P_CutMP_JA_FFS_sum_map_smul__b88492d3884a
