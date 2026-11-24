-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_eval__mul_block_of_isMultiHomog_db091611cf8f
-- name    : P2M_GroundTheory_Heights__Heights_eval__mul_block_of_isMultiHomog_db091611cf8f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:32:40.313948+00:00
-- url     : https://prove2.me/theorems/f8f9d924-423b-45db-91fb-917f66e7b2b6
-- title:
--   P2 M Ground Theory Heights  Heights eval  mul block of is Multi Homog db091611cf8f: P2 M Ground Theory Heights  Heights eval  mul block of is Multi Homog db091611cf8f
-- statement:
--   The P2 M Ground Theory Heights  Heights eval  mul block of is Multi Homog db091611cf8f construction uses the P2 M Ground Theory Heights  Heights eval  mul block of is Multi Homog db091611cf8f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitChartTerm.lean#L11-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitChartTerm.lean#L11-L26

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitChartTerm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartTerm
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
variable {ι : Type} [Fintype ι] {n : ι → ℕ}

theorem P2M_GroundTheory_Heights__Heights_eval__mul_block_of_isMultiHomog_db091611cf8f {R : Type*} [CommRing R] (s : MvPolynomial (Coord n) ℤ)
    (a : ι → ℕ) (hs : Geo.IsMultiHomog (ι := blockIdx n) s a) (g : ℤ →+* R) (y : Coord n → R)
    (t : ι → R) :
    eval₂ g (fun p ↦ y p * t p.1) s = eval₂ g y s * ∏ k, t k ^ a k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«eval₂_mul_block_of_isMultiHomog» := P2M_GroundTheory_Heights__Heights_eval__mul_block_of_isMultiHomog_db091611cf8f
