-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_ERam_evD_eqv
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam.evD_eqv
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:35:00.757938+00:00
-- url     : https://prove2.me/theorems/c4cba6d7-e05c-49c3-b4c5-796ea446409a
-- title:
--   ERam: ev D eqv
-- statement:
--   The ERam construction uses the ev D eqv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/EigRamCore.lean#L70-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/EigRamCore.lean#L70-L93

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

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam.evD_eqv (χ χ' : O →+* k) {n : ℕ} (b : Fin n → O) (c : Fin n → k) (h : IsEqv χ b c) (a : O) :
    χ' a * evD χ' b c = χ a * evD χ' b c := by sorry
