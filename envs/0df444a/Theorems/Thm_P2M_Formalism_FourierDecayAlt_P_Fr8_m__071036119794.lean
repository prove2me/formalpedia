-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr8_m__071036119794
-- name    : P2M_Formalism_FourierDecayAlt_P_Fr8_m__071036119794
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:02:19.998496+00:00
-- url     : https://prove2.me/theorems/3c9936fe-4df3-4333-bcc0-d84949bd138d
-- title:
--   P2 M Formalism Fourier Decay Alt P Fr8 m  071036119794: P2 M Formalism Fourier Decay Alt P Fr8 m  071036119794
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Fr8 m  071036119794 construction uses the P2 M Formalism Fourier Decay Alt P Fr8 m  071036119794 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GaussFormMinusLetter.lean#L152-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GaussFormMinusLetter.lean#L152-L153

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussFormMinusLetter
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr8
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S] {r : ℕ}

theorem P2M_Formalism_FourierDecayAlt_P_Fr8_m__071036119794 (L : LevelData A r) : L.ζ ∈ zfns L := by sorry

alias «Formalism».«FourierDecayAlt».«P».«Fr8».«mζ» := P2M_Formalism_FourierDecayAlt_P_Fr8_m__071036119794
