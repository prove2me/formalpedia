-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_span_secs_le_b24ff46a355a
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_span_secs_le_b24ff46a355a
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T06:22:01.812946+00:00
-- url     : https://prove2.me/theorems/5b9947a2-12c8-43aa-8c6a-b56a48f3ba7e
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Sub System span secs le b24ff46a355a: P2 M Ground Theory Heights  Heights Kleiman Sub System span secs le b24ff46a355a
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Sub System span secs le b24ff46a355a construction uses the P2 M Ground Theory Heights  Heights Kleiman Sub System span secs le b24ff46a355a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PNefPlusAmple.lean#L55-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PNefPlusAmple.lean#L55-L59

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_span_secs_le_b24ff46a355a (F : SubSystem k x Ω) (I : Chart x) :
    Submodule.span (chartRing k x I) (F.secs : Set Ω) ≤ F.sub I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SubSystem».«span_secs_le» := P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_span_secs_le_b24ff46a355a
