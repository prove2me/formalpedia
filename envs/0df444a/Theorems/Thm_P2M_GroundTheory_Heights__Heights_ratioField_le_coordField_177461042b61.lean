-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ratioField_le_coordField_177461042b61
-- name    : P2M_GroundTheory_Heights__Heights_ratioField_le_coordField_177461042b61
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:46:33.268406+00:00
-- url     : https://prove2.me/theorems/100b9767-4884-4085-8354-1011ee72462b
-- title:
--   P2 M Ground Theory Heights  Heights ratio Field le coord Field 177461042b61: P2 M Ground Theory Heights  Heights ratio Field le coord Field 177461042b61
-- statement:
--   The P2 M Ground Theory Heights  Heights ratio Field le coord Field 177461042b61 construction uses the P2 M Ground Theory Heights  Heights ratio Field le coord Field 177461042b61 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/HeightOrbitCenter.lean#L17-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/HeightOrbitCenter.lean#L17-L22

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitCenter
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
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G
noncomputable section
variable {ι : Type} {n : ι → ℕ}

theorem P2M_GroundTheory_Heights__Heights_ratioField_le_coordField_177461042b61 (x : Cone n (AlgebraicClosure ℚ)) :
    ratioField x ≤ coordField x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ratioField_le_coordField» := P2M_GroundTheory_Heights__Heights_ratioField_le_coordField_177461042b61
