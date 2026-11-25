-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_value_ne_zero_9e9fada13d9a
-- name    : P2M_GroundTheory_Heights__Heights_value_ne_zero_9e9fada13d9a
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:41:48.77481+00:00
-- url     : https://prove2.me/theorems/020b24cc-dd71-5966-9f0b-9c6395650078
-- title:
--   P2 M Ground Theory Heights  Heights value ne zero 9e9fada13d9a: P2 M Ground Theory Heights  Heights value ne zero 9e9fada13d9a
-- statement:
--   The P2 M Ground Theory Heights  Heights value ne zero 9e9fada13d9a construction uses the P2 M Ground Theory Heights  Heights value ne zero 9e9fada13d9a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FinrankFibreAtOfIsInvertibleSheaf.lean#L189-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FinrankFibreAtOfIsInvertibleSheaf.lean#L189-L194

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InvertibleSheaf
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FinrankFibreAtOfIsInvertibleSheaf
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
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace TensorProduct GroundTheory.Arith.SchemeCoh
universe u
noncomputable section
variable {X : Scheme.{u}} (L : X.Modules)
variable {L}
variable {p : X} {φ : locRing X p →+* ℂ}

theorem P2M_GroundTheory_Heights__Heights_value_ne_zero_9e9fada13d9a {U : X.Opens} (hp : p ∈ U) {e : ((preMod X).obj L).obj (op U)}
    (he : IsBasisOn ((preMod X).obj L) U e) : value φ hp e ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«value_ne_zero» := P2M_GroundTheory_Heights__Heights_value_ne_zero_9e9fada13d9a
