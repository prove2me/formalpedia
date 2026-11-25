-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_multiset_prod_sub_dvd
-- name    : ReciprocityTheory.ChartRestriction.G.Sh.PTb.multiset_prod_sub_dvd
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:35:00.792821+00:00
-- url     : https://prove2.me/theorems/8062c466-b070-4983-a6fb-7dd5d083729e
-- title:
--   PTb: multiset prod sub dvd
-- statement:
--   The PTb construction uses the multiset prod sub dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/CardToMultisetEqDegree.lean#L10-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/CardToMultisetEqDegree.lean#L10-L43

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

theorem ReciprocityTheory.ChartRestriction.G.Sh.PTb.multiset_prod_sub_dvd {S ι : Type*} [CommRing S] (t : S) (k : ℕ) (x y : ι → S)
    (hx : ∀ i, t ∣ x i) (hy : ∀ i, t ∣ y i) (hxy : ∀ i, t ^ k ∣ x i - y i) :
    ∀ s : Multiset ι, s ≠ 0 →
      t ^ (k + Multiset.card s - 1) ∣ (s.map x).prod - (s.map y).prod := by sorry
