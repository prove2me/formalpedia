-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_X_mem_orbitCenter_0f3e436ccb1d
-- name    : P2M_GroundTheory_Heights__Heights_X_mem_orbitCenter_0f3e436ccb1d
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:47:39.116832+00:00
-- url     : https://prove2.me/theorems/9718fdef-2664-4aaa-88a3-41c5d8e01d79
-- title:
--   P2 M Ground Theory Heights  Heights X mem orbit Center 0f3e436ccb1d: P2 M Ground Theory Heights  Heights X mem orbit Center 0f3e436ccb1d
-- statement:
--   The P2 M Ground Theory Heights  Heights X mem orbit Center 0f3e436ccb1d construction uses the P2 M Ground Theory Heights  Heights X mem orbit Center 0f3e436ccb1d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/HeightOrbitCenter.lean#L42-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/HeightOrbitCenter.lean#L42-L47

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
variable [Fintype ι]
variable [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_X_mem_orbitCenter_0f3e436ccb1d (x : Cone n (AlgebraicClosure ℚ)) (v : FinitePlace (coordField x))
    (k : ι) (i : Fin (n k + 1)) (hi : v (coordVec x k i) < ⨆ j, v (coordVec x k j)) :
    (X ⟨k, i⟩ : MvPolynomial (Coord n) ℤ) ∈ orbitCenter x v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«X_mem_orbitCenter» := P2M_GroundTheory_Heights__Heights_X_mem_orbitCenter_0f3e436ccb1d
