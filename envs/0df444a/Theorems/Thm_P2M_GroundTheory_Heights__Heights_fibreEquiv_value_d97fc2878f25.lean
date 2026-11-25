-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_fibreEquiv_value_d97fc2878f25
-- name    : P2M_GroundTheory_Heights__Heights_fibreEquiv_value_d97fc2878f25
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:46:30.152976+00:00
-- url     : https://prove2.me/theorems/5ee854bd-79bd-45ec-9dd9-989fa4017197
-- title:
--   P2 M Ground Theory Heights  Heights fibre Equiv value d97fc2878f25: P2 M Ground Theory Heights  Heights fibre Equiv value d97fc2878f25
-- statement:
--   The P2 M Ground Theory Heights  Heights fibre Equiv value d97fc2878f25 construction uses the P2 M Ground Theory Heights  Heights fibre Equiv value d97fc2878f25 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FinrankFibreAtOfIsInvertibleSheaf.lean#L170-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FinrankFibreAtOfIsInvertibleSheaf.lean#L170-L174

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

theorem P2M_GroundTheory_Heights__Heights_fibreEquiv_value_d97fc2878f25 {U : X.Opens} (hp : p ∈ U) {e : ((preMod X).obj L).obj (op U)}
    (he : IsBasisOn ((preMod X).obj L) U e) : fibreEquiv φ hp he (value φ hp e) = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«fibreEquiv_value» := P2M_GroundTheory_Heights__Heights_fibreEquiv_value_d97fc2878f25
