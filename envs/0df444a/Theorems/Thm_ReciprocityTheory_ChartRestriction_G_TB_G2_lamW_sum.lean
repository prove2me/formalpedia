-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_G2_lamW_sum
-- name    : ReciprocityTheory.ChartRestriction.G.TB.G2.lamW_sum
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:39:59.157926+00:00
-- url     : https://prove2.me/theorems/d782b17d-2c42-47d4-81b3-1baf4de7b41c
-- title:
--   G2: lam W sum
-- statement:
--   The G2 construction uses the lam W sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/FoldrIterateDerivationEq.lean#L33-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/FoldrIterateDerivationEq.lean#L33-L37

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SumSplitsEvalTwoWord
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_FoldrIterateDerivationEq
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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.G2
variable {k : Type} [CommRing k] {d : ℕ}
variable {ι : Type} [Fintype ι] [DecidableEq ι] (ψ : List ι → k)

theorem ReciprocityTheory.ChartRestriction.G.TB.G2.lamW_sum (s : Finset ι) (f : ι → MvPolynomial ι k) :
    lamW ψ (∑ i ∈ s, f i) = ∑ i ∈ s, lamW ψ (f i) := by sorry
