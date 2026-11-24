-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_evalCone_coordVec_ne_zero_c6e0cd13558e
-- name    : P2M_GroundTheory_Heights__Heights_evalCone_coordVec_ne_zero_c6e0cd13558e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:46:00.096604+00:00
-- url     : https://prove2.me/theorems/3602ca5a-2c8f-4456-92e5-7a9c4907ef0c
-- title:
--   P2 M Ground Theory Heights  Heights eval Cone coord Vec ne zero c6e0cd13558e: P2 M Ground Theory Heights  Heights eval Cone coord Vec ne zero c6e0cd13558e
-- statement:
--   The P2 M Ground Theory Heights  Heights eval Cone coord Vec ne zero c6e0cd13558e construction uses the P2 M Ground Theory Heights  Heights eval Cone coord Vec ne zero c6e0cd13558e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/PHeightRecR.lean#L38-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/PHeightRecR.lean#L38-L48

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightRecR
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitDivVertical
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitFiniteSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitArchSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Comparison
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_PHeightRecR
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
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

theorem P2M_GroundTheory_Heights__Heights_evalCone_coordVec_ne_zero_c6e0cd13558e (x : Cone n (AlgebraicClosure ℚ)) (s : MvPolynomial (Coord n) ℤ)
    (a : ι → ℕ) (hs : Geo.IsMultiHomog (ι := blockIdx n) s a) (hW : s ∉ orbitIdeal x) :
    evalCone (coordVec x) s ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«evalCone_coordVec_ne_zero» := P2M_GroundTheory_Heights__Heights_evalCone_coordVec_ne_zero_c6e0cd13558e
