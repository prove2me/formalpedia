-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_logCardLength_term_of_not_5772e4436efb
-- name    : P2M_GroundTheory_Heights__Heights_logCardLength_term_of_not_5772e4436efb
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:47:19.204017+00:00
-- url     : https://prove2.me/theorems/c16084e3-dfb0-4deb-8733-32a689214151
-- title:
--   P2 M Ground Theory Heights  Heights log Card Length term of not 5772e4436efb: P2 M Ground Theory Heights  Heights log Card Length term of not 5772e4436efb
-- statement:
--   The P2 M Ground Theory Heights  Heights log Card Length term of not 5772e4436efb construction uses the P2 M Ground Theory Heights  Heights log Card Length term of not 5772e4436efb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLogCardLength.lean#L30-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLogCardLength.lean#L30-L33

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLogCardLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLogCardLength
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
noncomputable section
open GroundTheory.Heights₂.Heights.logCardLength
open Module
variable (R : Type) [CommRing R]
variable {R}

theorem P2M_GroundTheory_Heights__Heights_logCardLength_term_of_not_5772e4436efb (N : Type) [AddCommGroup N] [Module R N] (m : Ideal R) (hm : ¬ m.IsMaximal) :
    term R N m = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«logCardLength».«term_of_not» := P2M_GroundTheory_Heights__Heights_logCardLength_term_of_not_5772e4436efb
