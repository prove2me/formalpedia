-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_CVA_fbOf_nabVal
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.CVA.fbOf_nabVal
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:33:36.75839+00:00
-- url     : https://prove2.me/theorems/195fd663-3a2c-5833-818c-bd9b1d1eab31
-- title:
--   CVA: fb Of nab Val
-- statement:
--   The CVA construction uses the fb Of nab Val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/BiextChangeSecondFactor.lean#L414-L417
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/BiextChangeSecondFactor.lean#L414-L417

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

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.CVA.fbOf_nabVal (h : PS k 2 d) (w0 : O) (m : ℕ) (f : PS k 1 d) {ι : Type} [Fintype ι] (u : ι → Fin d → k)
    (P : MvPolynomial ι k) : (fbOf t hφ).nabVal k h w0 m f u P = B.nabVal k h w0 m f u P := by sorry
