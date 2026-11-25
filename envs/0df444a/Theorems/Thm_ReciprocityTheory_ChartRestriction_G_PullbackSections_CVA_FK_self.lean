-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_CVA_FK_self
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.CVA.FK_self
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:32:54.764301+00:00
-- url     : https://prove2.me/theorems/912d8109-9a21-4351-91d5-24a4ab72c5e9
-- title:
--   CVA: FK self
-- statement:
--   The CVA construction uses the FK self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/BiextChangeSecondFactor.lean#L376-L378
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/BiextChangeSecondFactor.lean#L376-L378

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogInv
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_BiextChangeSecondFactor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.LogPf
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.CVA
variable {R k O : Type} [CommRing R] [CommRing k] [Algebra ℚ k] [Algebra R k] [CommRing O] [StarRing O] {d : ℕ}
variable {B : FB k d O} (t : IntTie (algebraMap R k) B) (hφ : Function.Injective (algebraMap R k))

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.CVA.FK_self (B : FB k d O) : B.FK k = B.G.F := by sorry
