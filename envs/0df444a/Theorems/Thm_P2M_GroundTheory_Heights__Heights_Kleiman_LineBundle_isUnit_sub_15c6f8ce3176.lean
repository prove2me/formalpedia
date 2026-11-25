-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LineBundle_isUnit_sub_15c6f8ce3176
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_LineBundle_isUnit_sub_15c6f8ce3176
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:12:26.447494+00:00
-- url     : https://prove2.me/theorems/e7f75f8d-ffae-5e4a-84e8-7770204b1a79
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Line Bundle is Unit sub 15c6f8ce3176: P2 M Ground Theory Heights  Heights Kleiman Line Bundle is Unit sub 15c6f8ce3176
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Line Bundle is Unit sub 15c6f8ce3176 construction uses the P2 M Ground Theory Heights  Heights Kleiman Line Bundle is Unit sub 15c6f8ce3176 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PNefPlusAmple.lean#L92-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PNefPlusAmple.lean#L92-L94

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsJoin
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PNefPlusAmple
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_LineBundle_isUnit_sub_15c6f8ce3176 (Q : LineBundle k x) (I : Chart x) : IsUnit (Q.sub I) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«LineBundle».«isUnit_sub» := P2M_GroundTheory_Heights__Heights_Kleiman_LineBundle_isUnit_sub_15c6f8ce3176
