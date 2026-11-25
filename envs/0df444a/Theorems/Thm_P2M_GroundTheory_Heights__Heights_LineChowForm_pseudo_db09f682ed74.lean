-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LineChowForm_pseudo_db09f682ed74
-- name    : P2M_GroundTheory_Heights__Heights_LineChowForm_pseudo_db09f682ed74
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:27:53.93325+00:00
-- url     : https://prove2.me/theorems/d3e877c5-103d-4a5e-9457-b5bd0de34ad7
-- title:
--   P2 M Ground Theory Heights  Heights Line Chow Form pseudo db09f682ed74: P2 M Ground Theory Heights  Heights Line Chow Form pseudo db09f682ed74
-- statement:
--   The P2 M Ground Theory Heights  Heights Line Chow Form pseudo db09f682ed74 construction uses the P2 M Ground Theory Heights  Heights Line Chow Form pseudo db09f682ed74 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LineInhabitant.lean#L52-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LineInhabitant.lean#L52-L76

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LineInhabitant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.LineChowForm
variable {F : Type*} [Field F]
variable {F : Type*} [Field F]

theorem P2M_GroundTheory_Heights__Heights_LineChowForm_pseudo_db09f682ed74 (g : MvPolynomial (Fin 2 × Fin 2) F) :
    ∃ (N : ℕ) (q r : MvPolynomial (Fin 2 × Fin 2) F),
      X (0,0) ^ N * g = q * D2 + r ∧ substZeroOneOne r = r := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LineChowForm».«pseudo» := P2M_GroundTheory_Heights__Heights_LineChowForm_pseudo_db09f682ed74
