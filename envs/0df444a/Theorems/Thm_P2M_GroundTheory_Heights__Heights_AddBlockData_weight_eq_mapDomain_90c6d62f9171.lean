-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AddBlockData_weight_eq_mapDomain_90c6d62f9171
-- name    : P2M_GroundTheory_Heights__Heights_AddBlockData_weight_eq_mapDomain_90c6d62f9171
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:15:32.201383+00:00
-- url     : https://prove2.me/theorems/eab91193-ec31-446a-97fa-5c95bacbdc7e
-- title:
--   P2 M Ground Theory Heights  Heights Add Block Data weight eq map Domain 90c6d62f9171: P2 M Ground Theory Heights  Heights Add Block Data weight eq map Domain 90c6d62f9171
-- statement:
--   The P2 M Ground Theory Heights  Heights Add Block Data weight eq map Domain 90c6d62f9171 construction uses the P2 M Ground Theory Heights  Heights Add Block Data weight eq map Domain 90c6d62f9171 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/WeightEqMapDomain.lean#L17-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/WeightEqMapDomain.lean#L17-L26

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_WeightEqMapDomain
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
open MvPolynomial
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
open GroundTheory.Heights₂.Heights.AddBlockData
variable {P : ArithVariety n} (D : AddBlockData P)

theorem P2M_GroundTheory_Heights__Heights_AddBlockData_weight_eq_mapDomain_90c6d62f9171 (s : Coord D.extSizes →₀ ℕ) :
    ⇑(s.mapDomain Sigma.fst) = Finsupp.weight (coordDeg D.extSizes) s := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AddBlockData».«weight_eq_mapDomain» := P2M_GroundTheory_Heights__Heights_AddBlockData_weight_eq_mapDomain_90c6d62f9171
