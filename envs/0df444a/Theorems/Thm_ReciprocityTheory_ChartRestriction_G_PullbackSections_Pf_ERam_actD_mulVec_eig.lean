-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_ERam_actD_mulVec_eig
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam.actD_mulVec_eig
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T14:14:59.533564+00:00
-- url     : https://prove2.me/theorems/07cfcbc5-f9c5-45eb-b01a-04d940aa8f8b
-- title:
--   ERam: act D mul Vec eig
-- statement:
--   The ERam construction uses the act D mul Vec eig property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/EigRamCore.lean#L34-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/EigRamCore.lean#L34-L45

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

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam.actD_mulVec_eig (M : O →+* Matrix (Fin d) (Fin d) k) (χ : O →+* k) {n : ℕ} (b : Fin n → O) (c : Fin n → k)
    (v : Fin d → k) (hv : ∀ a, (M a).mulVec v = χ a • v) : (actD M b c).mulVec v = evD χ b c • v := by sorry
