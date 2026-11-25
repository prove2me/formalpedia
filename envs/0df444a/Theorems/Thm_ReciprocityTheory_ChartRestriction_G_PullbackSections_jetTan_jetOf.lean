-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_jetTan_jetOf
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.jetTan_jetOf
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T15:43:49.602213+00:00
-- url     : https://prove2.me/theorems/ada1e374-47ae-4a5e-bb4b-b3d21a2a5520
-- title:
--   Pullback Sections: jet Tan jet Of
-- statement:
--   The Pullback Sections construction uses the jet Tan jet Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/HolJetF.lean#L88-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/HolJetF.lean#L88-L132

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetF
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections
open AlgebraicGeometry CategoryTheory Opposite Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt
open scoped ContDiff
variable {Y : Scheme.{0}}
variable {g : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.jetTan_jetOf (ℓ : Fin 1 × Fin g) (θ : (Fin g → ℂ) → ℂ) :
    (jetTan ℓ : Jet ℂ (Fin 1 × Fin g) (0 + 1) →ₐ[ℂ] DualNumber ℂ) (jetOf (0 + 1) θ) =
      TrivSqZeroExt.inl (θ 0) + TrivSqZeroExt.inr (fderiv ℂ θ 0 (Pi.single ℓ.2 1)) := by sorry
