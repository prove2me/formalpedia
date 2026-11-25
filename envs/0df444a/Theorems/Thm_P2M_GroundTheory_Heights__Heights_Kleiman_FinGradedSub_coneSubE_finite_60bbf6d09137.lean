-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_coneSubE_finite_60bbf6d09137
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_coneSubE_finite_60bbf6d09137
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:54:07.634616+00:00
-- url     : https://prove2.me/theorems/9fc0ab78-4d91-51ee-b8fd-189589b85c8a
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Fin Graded Sub cone Sub E finite 60bbf6d09137: P2 M Ground Theory Heights  Heights Kleiman Fin Graded Sub cone Sub E finite 60bbf6d09137
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Fin Graded Sub cone Sub E finite 60bbf6d09137 construction uses the P2 M Ground Theory Heights  Heights Kleiman Fin Graded Sub cone Sub E finite 60bbf6d09137 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeVanishCone.lean#L194-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeVanishCone.lean#L194-L214

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_AlgebraMapMemChartRingLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeTailLoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeVanishCone
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
universe u v w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
  (M : FinGradedSub (S := S) (x := x) E)

theorem P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_coneSubE_finite_60bbf6d09137 : Module.Finite (Poly S N) M.coneSubE := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«FinGradedSub».«coneSubE_finite» := P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_coneSubE_finite_60bbf6d09137
