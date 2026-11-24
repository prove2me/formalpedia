-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_mConeMap_of_isMultiHomog_f3a1bcb1fd3a
-- name    : P2M_GroundTheory_Heights__Heights_mConeMap_of_isMultiHomog_f3a1bcb1fd3a
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:35:49.836078+00:00
-- url     : https://prove2.me/theorems/3d1d57e9-c456-4950-9612-6fd3ecf55519
-- title:
--   P2 M Ground Theory Heights  Heights m Cone Map of is Multi Homog f3a1bcb1fd3a: P2 M Ground Theory Heights  Heights m Cone Map of is Multi Homog f3a1bcb1fd3a
-- statement:
--   The P2 M Ground Theory Heights  Heights m Cone Map of is Multi Homog f3a1bcb1fd3a construction uses the P2 M Ground Theory Heights  Heights m Cone Map of is Multi Homog f3a1bcb1fd3a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/PHeightRecR.lean#L19-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/PHeightRecR.lean#L19-L36

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
omit [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_mConeMap_of_isMultiHomog_f3a1bcb1fd3a {Ω : Type*} [Field Ω] (y : Coord n → Ω)
    (s : MvPolynomial (Coord n) ℤ) (a : ι → ℕ) (hs : Geo.IsMultiHomog (ι := blockIdx n) s a) :
    Geo.mConeMap (ι := blockIdx n) y s = C (eval₂ (Int.castRingHom Ω) y s) * ∏ k, X k ^ a k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«mConeMap_of_isMultiHomog» := P2M_GroundTheory_Heights__Heights_mConeMap_of_isMultiHomog_f3a1bcb1fd3a
