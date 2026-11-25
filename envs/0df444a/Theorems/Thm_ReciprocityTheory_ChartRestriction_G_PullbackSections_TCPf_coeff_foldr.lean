-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_TCPf_coeff_foldr
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.TCPf.coeff_foldr
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:33:35.973373+00:00
-- url     : https://prove2.me/theorems/116d4d99-b9af-429a-97cd-438c51f1d8bb
-- title:
--   TCPf: coeff foldr
-- statement:
--   The TCPf construction uses the coeff foldr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/TaylorComp.lean#L57-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/TaylorComp.lean#L57-L66

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_TaylorComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogChain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_TaylorComp
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.TCPf
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.PullbackSections
open scoped ContDiff Topology
variable {σ : Type}

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.TCPf.coeff_foldr (l : List σ) (m : σ →₀ ℕ) : ∃ c : ℂ, c ≠ 0 ∧ ∀ F : MvPowerSeries σ ℂ,
    coeff m (l.foldr (fun q G => pderiv ℂ q G) F) = c * coeff (m + (l.map fun q => Finsupp.single q 1).sum) F := by sorry
