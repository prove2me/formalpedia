-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_restrictData_id_2d88ef9d3ccb
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_restrictData_id_2d88ef9d3ccb
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:28:19.400886+00:00
-- url     : https://prove2.me/theorems/fe62aa57-da4c-4dee-b531-6d73b7d18375
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman restrict Data id 2d88ef9d3ccb: P2 M Ground Theory Heights  Heights Kleiman restrict Data id 2d88ef9d3ccb
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman restrict Data id 2d88ef9d3ccb construction uses the P2 M Ground Theory Heights  Heights Kleiman restrict Data id 2d88ef9d3ccb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/AlgebraMapMemChartRingLine.lean#L370-L375
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/AlgebraMapMemChartRingLine.lean#L370-L375

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_restrictData_id_2d88ef9d3ccb (Q : SubSystem S x Ω) :
    RestrictData (K' := Ω) Q (y := x) (fun _ h => h) Q id := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«restrictData_id» := P2M_GroundTheory_Heights__Heights_Kleiman_restrictData_id_2d88ef9d3ccb
