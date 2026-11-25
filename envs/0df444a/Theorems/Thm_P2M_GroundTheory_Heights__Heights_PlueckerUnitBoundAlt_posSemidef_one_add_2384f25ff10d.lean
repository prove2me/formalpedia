-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PlueckerUnitBoundAlt_posSemidef_one_add_2384f25ff10d
-- name    : P2M_GroundTheory_Heights__Heights_PlueckerUnitBoundAlt_posSemidef_one_add_2384f25ff10d
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:14:22.518864+00:00
-- url     : https://prove2.me/theorems/17b913de-ecf4-5af4-ad28-928b8b6009a4
-- title:
--   P2 M Ground Theory Heights  Heights Pluecker Unit Bound Alt pos Semidef one add 2384f25ff10d: P2 M Ground Theory Heights  Heights Pluecker Unit Bound Alt pos Semidef one add 2384f25ff10d
-- statement:
--   The P2 M Ground Theory Heights  Heights Pluecker Unit Bound Alt pos Semidef one add 2384f25ff10d construction uses the P2 M Ground Theory Heights  Heights Pluecker Unit Bound Alt pos Semidef one add 2384f25ff10d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PPlueckerUnitBound.lean#L12-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PPlueckerUnitBound.lean#L12-L14

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PPlueckerUnitBound
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
open Matrix Finset
open scoped ComplexOrder
open GroundTheory.Heights₂.Heights.PlueckerUnitBoundAlt

theorem P2M_GroundTheory_Heights__Heights_PlueckerUnitBoundAlt_posSemidef_one_add_2384f25ff10d {j m : ℕ} (Z : Matrix (Fin j) (Fin m) ℂ) :
    (1 + Z * Zᴴ).PosSemidef := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PlueckerUnitBoundAlt».«posSemidef_one_add» := P2M_GroundTheory_Heights__Heights_PlueckerUnitBoundAlt_posSemidef_one_add_2384f25ff10d
