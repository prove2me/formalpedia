-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_EigA_idem_eig
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA.idem_eig
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:37:44.747908+00:00
-- url     : https://prove2.me/theorems/2f6feae2-7bcf-5587-832d-190fd8879d09
-- title:
--   Eig A: idem eig
-- statement:
--   The Eig A construction uses the idem eig property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/BiextCoeffSecondLinear.lean#L154-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/BiextCoeffSecondLinear.lean#L154-L167

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_FormalGroupCoeffSecondLinear
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_BiextCoeffSecondLinear
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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA.idem_eig {d : ℕ} {O k : Type} [CommRing O] [CommRing k] (M : O →+* Matrix (Fin d) (Fin d) k) (χ : O →+* k)
    {n : ℕ} (b : Fin n → O) (c : Fin n → k) (a : O) (m : Fin n → Fin n → ℤ)
    (hb : ∀ i, a * b i = ∑ j, m i j • b j) (hc : ∀ j, ∑ i, (m i j : k) * c i = χ a * c j) :
    M a * ∑ i, c i • M (b i) = χ a • ∑ i, c i • M (b i) := by sorry
