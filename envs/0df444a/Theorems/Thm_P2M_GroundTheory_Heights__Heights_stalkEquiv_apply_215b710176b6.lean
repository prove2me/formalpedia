-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_stalkEquiv_apply_215b710176b6
-- name    : P2M_GroundTheory_Heights__Heights_stalkEquiv_apply_215b710176b6
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:50:54.459006+00:00
-- url     : https://prove2.me/theorems/07054c0d-b360-42d2-a4da-fa5ff366bc9c
-- title:
--   P2 M Ground Theory Heights  Heights stalk Equiv apply 215b710176b6: P2 M Ground Theory Heights  Heights stalk Equiv apply 215b710176b6
-- statement:
--   The P2 M Ground Theory Heights  Heights stalk Equiv apply 215b710176b6 construction uses the P2 M Ground Theory Heights  Heights stalk Equiv apply 215b710176b6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FinrankFibreAtOfIsInvertibleSheaf.lean#L123-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FinrankFibreAtOfIsInvertibleSheaf.lean#L123-L125

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

theorem P2M_GroundTheory_Heights__Heights_stalkEquiv_apply_215b710176b6 {U : X.Opens} {p : X} (hp : p ∈ U) {e : ((preMod X).obj L).obj (op U)}
    (he : IsBasisOn ((preMod X).obj L) U e) (r : locRing X p) :
    stalkEquiv hp he r = r • germM hp e := by sorry

alias «GroundTheory».«Heights₂».«Heights».«stalkEquiv_apply» := P2M_GroundTheory_Heights__Heights_stalkEquiv_apply_215b710176b6
