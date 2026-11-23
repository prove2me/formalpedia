-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Mx7_modY1__87e636a5f50a
-- name    : P2M_Formalism_FourierDecayAlt_P_Mx7_modY1__87e636a5f50a
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:46:19.716264+00:00
-- url     : https://prove2.me/theorems/0d111bb5-7538-406e-bd42-eb8c6d5f4162
-- title:
--   P2 M Formalism Fourier Decay Alt P Mx7 mod Y1  87e636a5f50a: P2 M Formalism Fourier Decay Alt P Mx7 mod Y1  87e636a5f50a
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Mx7 mod Y1  87e636a5f50a construction uses the P2 M Formalism Fourier Decay Alt P Mx7 mod Y1  87e636a5f50a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightedSumDifferenceIdentity.lean#L1241-L1255
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightedSumDifferenceIdentity.lean#L1241-L1255

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

theorem P2M_Formalism_FourierDecayAlt_P_Mx7_modY1__87e636a5f50a (hSc : SSScalar) (hSh : SSShift) (hR : RhoUp) (hLF : LevFns) (hLNs : LevNabs) (P : Par) (Y : ℂ)
    (h0 : ∀ π, xC P π Y ≠ 0) (h1 : ∀ π, xC P π (Y + 1) ≠ 0) :
    mA P (Y + 1) * t22 P Y = t22 P Y * mA P Y := by sorry

alias «Formalism».«FourierDecayAlt».«P».«Mx7».«modY1'» := P2M_Formalism_FourierDecayAlt_P_Mx7_modY1__87e636a5f50a
