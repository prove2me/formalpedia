-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr5_mem__i_7172e6a0b2cd
-- name    : P2M_Formalism_FourierDecayAlt_P_Fr5_mem__i_7172e6a0b2cd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:03:31.884417+00:00
-- url     : https://prove2.me/theorems/885e2616-d975-4a69-9c1a-ecf9855d98a0
-- title:
--   P2 M Formalism Fourier Decay Alt P Fr5 mem  i 7172e6a0b2cd: P2 M Formalism Fourier Decay Alt P Fr5 mem  i 7172e6a0b2cd
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Fr5 mem  i 7172e6a0b2cd construction uses the P2 M Formalism Fourier Decay Alt P Fr5 mem  i 7172e6a0b2cd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FreeOf2OfFourEntries.lean#L190-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FreeOf2OfFourEntries.lean#L190-L191

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QEFirstMulSecondEqSwap
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FreeOf2OfFourEntries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr5
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S] {r : ℕ}

theorem P2M_Formalism_FourierDecayAlt_P_Fr5_mem__i_7172e6a0b2cd (L : LevelData A r) : L.ζi ∈ zfns L := by sorry

alias «Formalism».«FourierDecayAlt».«P».«Fr5».«mem_ζi» := P2M_Formalism_FourierDecayAlt_P_Fr5_mem__i_7172e6a0b2cd
