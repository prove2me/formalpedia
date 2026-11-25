-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_UH_hermForm_sub_mat
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.UH.hermForm_sub_mat
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:33:26.429589+00:00
-- url     : https://prove2.me/theorems/d3eb4693-c84b-5d0a-a134-dd3cdf7239ea
-- title:
--   UH: herm Form sub mat
-- statement:
--   The UH construction uses the herm Form sub mat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/UnitHmA.lean#L29-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/UnitHmA.lean#L29-L31

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_UnitHmA
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.UH
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {g : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.UH.hermForm_sub_mat (H₁ H₂ : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    hermForm (H₁ - H₂) z w = hermForm H₁ z w - hermForm H₂ z w := by sorry
