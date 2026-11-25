-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_QuasiFiniteSheets_hasSheetsOff_empty_e8cbdc6b748b
-- name    : P2M_GroundTheory_Heights__Heights_QuasiFiniteSheets_hasSheetsOff_empty_e8cbdc6b748b
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:16:26.974883+00:00
-- url     : https://prove2.me/theorems/7b77d33b-c701-4f7f-a999-0da15ebf75d1
-- title:
--   P2 M Ground Theory Heights  Heights Quasi Finite Sheets has Sheets Off empty e8cbdc6b748b: P2 M Ground Theory Heights  Heights Quasi Finite Sheets has Sheets Off empty e8cbdc6b748b
-- statement:
--   The P2 M Ground Theory Heights  Heights Quasi Finite Sheets has Sheets Off empty e8cbdc6b748b construction uses the P2 M Ground Theory Heights  Heights Quasi Finite Sheets has Sheets Off empty e8cbdc6b748b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PQuasiFiniteSheets.lean#L25-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PQuasiFiniteSheets.lean#L25-L30

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsQuasiFiniteSheets
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsPrimeQuasiFiniteSheets
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsPrimePairMeetImage
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PQuasiFiniteSheets
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
open GroundTheory.Heights₂.Heights.QuasiFiniteSheets
variable {n d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_QuasiFiniteSheets_hasSheetsOff_empty_e8cbdc6b748b (A : Matrix (Fin d) (Fin n) ℂ) : HasSheetsOff ∅ A 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«QuasiFiniteSheets».«hasSheetsOff_empty» := P2M_GroundTheory_Heights__Heights_QuasiFiniteSheets_hasSheetsOff_empty_e8cbdc6b748b
