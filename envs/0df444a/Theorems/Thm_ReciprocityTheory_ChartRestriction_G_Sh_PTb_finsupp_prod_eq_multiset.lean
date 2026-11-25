-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_finsupp_prod_eq_multiset
-- name    : ReciprocityTheory.ChartRestriction.G.Sh.PTb.finsupp_prod_eq_multiset
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:34:37.947489+00:00
-- url     : https://prove2.me/theorems/436a143b-5051-4164-a798-b56761a3419c
-- title:
--   PTb: finsupp prod eq multiset
-- statement:
--   The PTb construction uses the finsupp prod eq multiset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/CardToMultisetEqDegree.lean#L45-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/CardToMultisetEqDegree.lean#L45-L54

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_TangentEqLcZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_CardToMultisetEqDegree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Sh ReciprocityTheory.ChartRestriction.G.Sh.PTb
open MvPowerSeries ReciprocityTheory.PGsh
noncomputable section

theorem ReciprocityTheory.ChartRestriction.G.Sh.PTb.finsupp_prod_eq_multiset {S ι : Type*} [CommMonoid S] (x : ι → S) (e : ι →₀ ℕ) :
    e.prod (fun i m => x i ^ m) = (e.toMultiset.map x).prod := by sorry
