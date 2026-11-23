-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr5_mem__bi_956546b22979
-- name    : P2M_Formalism_FourierDecayAlt_P_Fr5_mem__bi_956546b22979
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:03:44.25672+00:00
-- url     : https://prove2.me/theorems/cf6bf68b-956e-494c-8e45-12554350ffa4
-- title:
--   P2 M Formalism Fourier Decay Alt P Fr5 mem  bi 956546b22979: P2 M Formalism Fourier Decay Alt P Fr5 mem  bi 956546b22979
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Fr5 mem  bi 956546b22979 construction uses the P2 M Formalism Fourier Decay Alt P Fr5 mem  bi 956546b22979 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FreeOf2OfFourEntries.lean#L194-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FreeOf2OfFourEntries.lean#L194-L195

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

theorem P2M_Formalism_FourierDecayAlt_P_Fr5_mem__bi_956546b22979 (L : LevelData A r) : L.ζbi ∈ zfns L := by sorry

alias «Formalism».«FourierDecayAlt».«P».«Fr5».«mem_ζbi» := P2M_Formalism_FourierDecayAlt_P_Fr5_mem__bi_956546b22979
