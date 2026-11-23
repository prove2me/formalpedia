-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Mx7_xEx_pair__9b8c59969b7c
-- name    : P2M_Formalism_FourierDecayAlt_P_Mx7_xEx_pair__9b8c59969b7c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:46:15.22879+00:00
-- url     : https://prove2.me/theorems/15d835fa-d960-4966-9871-dd6a2437be6d
-- title:
--   P2 M Formalism Fourier Decay Alt P Mx7 x Ex pair  9b8c59969b7c: P2 M Formalism Fourier Decay Alt P Mx7 x Ex pair  9b8c59969b7c
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Mx7 x Ex pair  9b8c59969b7c construction uses the P2 M Formalism Fourier Decay Alt P Mx7 x Ex pair  9b8c59969b7c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightedSumDifferenceIdentity.lean#L58-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightedSumDifferenceIdentity.lean#L58-L60

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedSumDifferenceIdentity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx7
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset

theorem P2M_Formalism_FourierDecayAlt_P_Mx7_xEx_pair__9b8c59969b7c (P : Par) (π : Ty P) (Y : ℂ) (l j : ℕ) (hl : l ∈ Icc 1 (P.k - 1)) (hjl : j ≠ l) :
    xEx P {j} π Y = xEx P {l, j} π Y * (Y + (rho P π l : ℂ)) := by sorry

alias «Formalism».«FourierDecayAlt».«P».«Mx7».«xEx_pair'» := P2M_Formalism_FourierDecayAlt_P_Mx7_xEx_pair__9b8c59969b7c
