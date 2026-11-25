-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_UH_herm_eq_of_im
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.UH.herm_eq_of_im
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:33:34.243108+00:00
-- url     : https://prove2.me/theorems/68429a78-211e-44f1-8c6d-051b81b70075
-- title:
--   UH: herm eq of im
-- statement:
--   The UH construction uses the herm eq of im property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/UnitHmA.lean#L42-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/UnitHmA.lean#L42-L70

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

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.UH.herm_eq_of_im {L : Type} [AddCommGroup L] (P : L →+ (Fin g → ℂ))
    (hP : Submodule.span ℝ (Set.range P) = ⊤) (H₁ H₂ : Matrix (Fin g) (Fin g) ℂ)
    (h : ∀ x y, (hermForm H₁ (P x) (P y)).im = (hermForm H₂ (P x) (P y)).im) : H₁ = H₂ := by sorry
