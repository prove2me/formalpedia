-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AddBlockData_extMap_component_ef6c391bfafd
-- name    : P2M_GroundTheory_Heights__Heights_AddBlockData_extMap_component_ef6c391bfafd
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:15:24.710872+00:00
-- url     : https://prove2.me/theorems/458e3a68-f43a-4e75-9913-f1d2c3d7bb4f
-- title:
--   P2 M Ground Theory Heights  Heights Add Block Data ext Map component ef6c391bfafd: P2 M Ground Theory Heights  Heights Add Block Data ext Map component ef6c391bfafd
-- statement:
--   The P2 M Ground Theory Heights  Heights Add Block Data ext Map component ef6c391bfafd construction uses the P2 M Ground Theory Heights  Heights Add Block Data ext Map component ef6c391bfafd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/WeightEqMapDomain.lean#L40-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/WeightEqMapDomain.lean#L40-L60

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

theorem P2M_GroundTheory_Heights__Heights_AddBlockData_extMap_component_ef6c391bfafd (m : Option ι → ℕ) (f : MvPolynomial (Coord D.extSizes) ℤ) :
    D.extMap (weightedHomogeneousComponent (coordDeg D.extSizes) m f) =
      monomial (Finsupp.equivFunOnFinite.symm m)
        (coeff (Finsupp.equivFunOnFinite.symm m) (D.extMap f)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AddBlockData».«extMap_component» := P2M_GroundTheory_Heights__Heights_AddBlockData_extMap_component_ef6c391bfafd
