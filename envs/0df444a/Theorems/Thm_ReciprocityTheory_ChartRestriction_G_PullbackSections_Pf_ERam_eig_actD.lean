-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_ERam_eig_actD
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam.eig_actD
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:11:45.958114+00:00
-- url     : https://prove2.me/theorems/e760dfc2-35c3-4f6f-912d-1dc949a439a8
-- title:
--   ERam: eig act D
-- statement:
--   The ERam construction uses the eig act D property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/EigRamCore.lean#L47-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/EigRamCore.lean#L47-L68

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_BiextCoeffSecondLinear
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_EigRamCore
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
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam
variable {O k : Type} [CommRing O] [CommRing k] {d : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam.eig_actD (M : O →+* Matrix (Fin d) (Fin d) k) (χ : O →+* k) {n : ℕ} (b : Fin n → O) (c : Fin n → k)
    (h : IsEqv χ b c) (a : O) : M a * actD M b c = χ a • actD M b c := by sorry
