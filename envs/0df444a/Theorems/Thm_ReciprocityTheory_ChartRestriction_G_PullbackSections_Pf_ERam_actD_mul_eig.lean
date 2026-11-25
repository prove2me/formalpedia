-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_ERam_actD_mul_eig
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam.actD_mul_eig
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:32:59.611774+00:00
-- url     : https://prove2.me/theorems/16726a6f-6949-5640-831e-541dfe785728
-- title:
--   ERam: act D mul eig
-- statement:
--   The ERam construction uses the act D mul eig property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/EigRamCore.lean#L105-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/EigRamCore.lean#L105-L117

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

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam.actD_mul_eig (M : O →+* Matrix (Fin d) (Fin d) k) (χ : O →+* k) {n n' : ℕ} (b : Fin n → O) (c : Fin n → k)
    (h : IsEqv χ b c) (b' : Fin n' → O) (c' : Fin n' → k) :
    actD M b c * actD M b' c' = evD χ b' c' • actD M b c := by sorry
