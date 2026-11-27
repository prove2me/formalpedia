-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ratStandard_isDualBasis_99a9af2cb50b
-- name    : P2M_GroundTheory_Heights__Heights_ratStandard_isDualBasis_99a9af2cb50b
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:42:04.848684+00:00
-- url     : https://prove2.me/theorems/fe829bb4-3a60-580d-ab5b-fde7cc590495
-- title:
--   P2 M Ground Theory Heights  Heights rat Standard is Dual Basis 99a9af2cb50b: P2 M Ground Theory Heights  Heights rat Standard is Dual Basis 99a9af2cb50b
-- statement:
--   The P2 M Ground Theory Heights  Heights rat Standard is Dual Basis 99a9af2cb50b construction uses the P2 M Ground Theory Heights  Heights rat Standard is Dual Basis 99a9af2cb50b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/DualModel.lean#L71-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/DualModel.lean#L71-L107

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_DualModel
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
open MvPolynomial NumberField Matrix
open scoped ComplexOrder
noncomputable section
variable {K : Type*} [Field K] [NumberField K]

theorem P2M_GroundTheory_Heights__Heights_ratStandard_isDualBasis_99a9af2cb50b (r : ℕ) :
    IsDualBasis (HermLattice.standard ℚ (r + 1)).lattice
      (fun j : Fin (r + 1) ↦ (Pi.single j (1 : ℚ) : Fin (r + 1) → ℚ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ratStandard_isDualBasis» := P2M_GroundTheory_Heights__Heights_ratStandard_isDualBasis_99a9af2cb50b
