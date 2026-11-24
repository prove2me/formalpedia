-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_isWeightedHomogeneous_map_of_isMultiHomog
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.isWeightedHomogeneous_map_of_isMultiHomog
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:07:41.192363+00:00
-- url     : https://prove2.me/theorems/0a279163-95d8-418e-9010-16226d0a9cd6
-- title:
--   Geo: is Weighted Homogeneous map of is Multi Homog
-- statement:
--   The Geo construction uses the is Weighted Homogeneous map of is Multi Homog property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterFibB.lean#L20-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterFibB.lean#L20-L31

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFibB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem ReciprocityTheory.ChartRestriction.G.Geo.isWeightedHomogeneous_map_of_isMultiHomog {s : MRing ι} {a : K → ℕ} (hs : IsMultiHomog s a) :
    IsWeightedHomogeneous (blkW ι) (map (Int.castRingHom ℂ) s) a := by sorry
