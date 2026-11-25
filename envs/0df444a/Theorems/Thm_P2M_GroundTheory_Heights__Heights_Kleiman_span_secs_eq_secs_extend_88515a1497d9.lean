-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_span_secs_eq_secs_extend_88515a1497d9
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_span_secs_eq_secs_extend_88515a1497d9
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T07:11:03.7565+00:00
-- url     : https://prove2.me/theorems/3b1d2892-c946-5530-a9c2-d09eccd64346
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman span secs eq secs extend 88515a1497d9: P2 M Ground Theory Heights  Heights Kleiman span secs eq secs extend 88515a1497d9
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman span secs eq secs extend 88515a1497d9 construction uses the P2 M Ground Theory Heights  Heights Kleiman span secs eq secs extend 88515a1497d9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PFiniteSections.lean#L161-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PFiniteSections.lean#L161-L189

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsTildeTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PFiniteSections
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
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {F : Type u} [Field F] [Algebra S F] [Algebra F Ω] [IsScalarTower S F Ω]
  [IsFractionRing S F]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_span_secs_eq_secs_extend_88515a1497d9 (Q : SubSystem S x Ω) :
    Submodule.span F (Q.secs : Set Ω) = (Q.extend F).secs := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«span_secs_eq_secs_extend» := P2M_GroundTheory_Heights__Heights_Kleiman_span_secs_eq_secs_extend_88515a1497d9
