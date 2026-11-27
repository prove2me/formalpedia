-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ratDoubled_isDualBasis_8bbf0f50c112
-- name    : P2M_GroundTheory_Heights__Heights_ratDoubled_isDualBasis_8bbf0f50c112
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T13:48:07.905519+00:00
-- url     : https://prove2.me/theorems/fab8b1a9-12db-4d72-9beb-1a08b1a3f997
-- title:
--   P2 M Ground Theory Heights  Heights rat Doubled is Dual Basis 8bbf0f50c112: P2 M Ground Theory Heights  Heights rat Doubled is Dual Basis 8bbf0f50c112
-- statement:
--   The P2 M Ground Theory Heights  Heights rat Doubled is Dual Basis 8bbf0f50c112 construction uses the P2 M Ground Theory Heights  Heights rat Doubled is Dual Basis 8bbf0f50c112 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/DualModel.lean#L142-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/DualModel.lean#L142-L184

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

theorem P2M_GroundTheory_Heights__Heights_ratDoubled_isDualBasis_8bbf0f50c112 (r : ℕ) :
    IsDualBasis (ratDoubled r).lattice
      (fun j : Fin (r + 1) ↦ (Pi.single j (1 / 2 : ℚ) : Fin (r + 1) → ℚ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ratDoubled_isDualBasis» := P2M_GroundTheory_Heights__Heights_ratDoubled_isDualBasis_8bbf0f50c112
