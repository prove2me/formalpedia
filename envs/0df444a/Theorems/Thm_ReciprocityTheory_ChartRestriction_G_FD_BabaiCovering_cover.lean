-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_BabaiCovering_cover
-- name    : ReciprocityTheory.ChartRestriction.G.FD.BabaiCovering.cover
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:46:59.988199+00:00
-- url     : https://prove2.me/theorems/ac1089c2-97b5-4a31-a135-801a81a0d8f7
-- title:
--   Babai Covering: cover
-- statement:
--   The Babai Covering construction uses the cover property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/BabaiCovering.lean#L63-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/BabaiCovering.lean#L63-L130

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_Transference
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_BabaiCovering
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.BabaiCovering
open Submodule Module
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

theorem ReciprocityTheory.ChartRestriction.G.FD.BabaiCovering.cover {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℝ V) (bd : ι → V)
    (hd : ∀ i j, inner ℝ (b i) (bd j) = if i = j then 1 else 0) (lam : ℝ) (hlam : 0 < lam)
    (hmin : ∀ x ∈ span ℤ (Set.range bd), x ≠ 0 → lam ≤ ‖x‖) (v : V) :
    ∃ x ∈ span ℤ (Set.range b),
      ‖v - x‖ ^ 2 ≤ (finrank ℝ V : ℝ) / 4 * ((finrank ℝ V : ℝ) ^ 2 / lam) ^ 2 := by sorry
