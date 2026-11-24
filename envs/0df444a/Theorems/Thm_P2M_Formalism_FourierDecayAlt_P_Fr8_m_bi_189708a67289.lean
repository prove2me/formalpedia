-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr8_m_bi_189708a67289
-- name    : P2M_Formalism_FourierDecayAlt_P_Fr8_m_bi_189708a67289
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:02:23.8168+00:00
-- url     : https://prove2.me/theorems/b876333f-6dbf-45e1-8696-021792e63d8c
-- title:
--   P2 M Formalism Fourier Decay Alt P Fr8 m bi 189708a67289: P2 M Formalism Fourier Decay Alt P Fr8 m bi 189708a67289
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Fr8 m bi 189708a67289 construction uses the P2 M Formalism Fourier Decay Alt P Fr8 m bi 189708a67289 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GaussFormMinusLetter.lean#L158-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GaussFormMinusLetter.lean#L158-L159

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

theorem P2M_Formalism_FourierDecayAlt_P_Fr8_m_bi_189708a67289 (L : LevelData A r) : L.ζbi ∈ zfns L := by sorry

alias «Formalism».«FourierDecayAlt».«P».«Fr8».«mζbi» := P2M_Formalism_FourierDecayAlt_P_Fr8_m_bi_189708a67289
