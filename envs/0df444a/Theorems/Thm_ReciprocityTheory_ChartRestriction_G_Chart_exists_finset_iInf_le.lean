-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_exists_finset_iInf_le
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.exists_finset_iInf_le
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:09:39.18628+00:00
-- url     : https://prove2.me/theorems/79560a1a-eb91-47d5-b6ef-d1ba91700828
-- title:
--   Chart: exists finset i Inf le
-- statement:
--   The Chart construction uses the exists finset i Inf le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/RankLin.lean#L13-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/RankLin.lean#L13-L26

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RankLin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
open Module
variable {V k : Type} [CommRing V] [IsDomain V] [IsPrincipalIdealRing V] [Field k] [Algebra V k] [FaithfulSMul V k]

theorem ReciprocityTheory.ChartRestriction.G.Chart.exists_finset_iInf_le {M : Type} [AddCommGroup M] [Module k M] [FiniteDimensional k M] {O : Type}
    (K : O → Submodule k M) : ∃ F : Finset O, ∀ b, (⨅ a ∈ F, K a) ≤ K b := by sorry
