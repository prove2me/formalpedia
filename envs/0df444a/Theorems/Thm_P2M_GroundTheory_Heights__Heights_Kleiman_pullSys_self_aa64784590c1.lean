-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_pullSys_self_aa64784590c1
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_pullSys_self_aa64784590c1
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T06:15:23.635119+00:00
-- url     : https://prove2.me/theorems/9dc659b9-2464-5fc5-b109-0a6e0f4bfdf3
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman pull Sys self aa64784590c1: P2 M Ground Theory Heights  Heights Kleiman pull Sys self aa64784590c1
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman pull Sys self aa64784590c1 construction uses the P2 M Ground Theory Heights  Heights Kleiman pull Sys self aa64784590c1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/AlgebraMapMemChartRingLine.lean#L350-L351
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/AlgebraMapMemChartRingLine.lean#L350-L351

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_AlgebraMapMemChartRingLine
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
open MvPolynomial Filter
noncomputable section
universe u v w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_pullSys_self_aa64784590c1 : pullSys (S := S) x x = twistSys S x 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«pullSys_self» := P2M_GroundTheory_Heights__Heights_Kleiman_pullSys_self_aa64784590c1
