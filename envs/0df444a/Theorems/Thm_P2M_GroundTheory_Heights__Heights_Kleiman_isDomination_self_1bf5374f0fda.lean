-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_isDomination_self_1bf5374f0fda
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_isDomination_self_1bf5374f0fda
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:27:56.866729+00:00
-- url     : https://prove2.me/theorems/9380286e-d025-4ef7-a851-7603a913dddc
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman is Domination self 1bf5374f0fda: P2 M Ground Theory Heights  Heights Kleiman is Domination self 1bf5374f0fda
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman is Domination self 1bf5374f0fda construction uses the P2 M Ground Theory Heights  Heights Kleiman is Domination self 1bf5374f0fda property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/AlgebraMapMemChartRingLine.lean#L353-L356
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/AlgebraMapMemChartRingLine.lean#L353-L356

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_isDomination_self_1bf5374f0fda : IsDomination S x x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«isDomination_self» := P2M_GroundTheory_Heights__Heights_Kleiman_isDomination_self_1bf5374f0fda
