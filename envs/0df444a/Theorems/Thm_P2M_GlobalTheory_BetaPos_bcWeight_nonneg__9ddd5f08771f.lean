-- Prove2me | Theorems.Thm_P2M_GlobalTheory_BetaPos_bcWeight_nonneg__9ddd5f08771f
-- name    : P2M_GlobalTheory_BetaPos_bcWeight_nonneg__9ddd5f08771f
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:04:39.149845+00:00
-- url     : https://prove2.me/theorems/ddb2ad75-2d4a-488c-9bcd-9203fcaf0566
-- title:
--   P2 M Global Theory Beta Pos bc Weight nonneg  9ddd5f08771f: P2 M Global Theory Beta Pos bc Weight nonneg  9ddd5f08771f
-- statement:
--   The P2 M Global Theory Beta Pos bc Weight nonneg  9ddd5f08771f construction uses the P2 M Global Theory Beta Pos bc Weight nonneg  9ddd5f08771f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/BetaSelfReNonneg.lean#L10-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/BetaSelfReNonneg.lean#L10-L14

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_LetterProductDoubleDegreeCount
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_BetaSelfReNonneg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset MeasureTheory
open GlobalTheory GlobalTheory.BetaPos

theorem P2M_GlobalTheory_BetaPos_bcWeight_nonneg__9ddd5f08771f (k r : ℕ) (T T' : ℝ) (q : (Fin r → ℂ) × ℂ) : 0 ≤ bcWeight k r T T' q := by sorry

alias «GlobalTheory».«BetaPos».«bcWeight_nonneg'» := P2M_GlobalTheory_BetaPos_bcWeight_nonneg__9ddd5f08771f
