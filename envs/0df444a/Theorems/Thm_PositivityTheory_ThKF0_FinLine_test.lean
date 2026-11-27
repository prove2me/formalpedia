-- Prove2me | Theorems.Thm_PositivityTheory_ThKF0_FinLine_test
-- name    : PositivityTheory.ThKF0.FinLine.test
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T14:00:50.663142+00:00
-- url     : https://prove2.me/theorems/f48970cc-9eff-4df0-8f81-96a78aaeaaa0
-- title:
--   Fin Line: test
-- statement:
--   The Fin Line construction uses the test property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/LagrangianUniqueness/Imports.lean#L108-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/LagrangianUniqueness/Imports.lean#L108-L145

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_LagrangianUniqueness_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.WeilM Filter Topology
open scoped Classical
noncomputable section
open PositivityTheory PositivityTheory.ThKF0 PositivityTheory.ThKF0.FinLine
variable {G : Type} [AddCommGroup G] [TopologicalSpace G] [NonarchimedeanAddGroup G]
variable {U₀ : OpenAddSubgroup G} (h₀ : IsCompact (U₀ : Set G)) {P : Set G} {l : (G → ℂ) →ₗ[ℂ] ℂ}
include h₀

theorem PositivityTheory.ThKF0.FinLine.test (hP0 : (0 : G) ∈ P) (h1 : ∀ p ∈ P, ∀ φ ∈ SB G, l (fun x => φ (x + p)) = l φ)
    (h2 : ∀ a ∉ P, ∃ χ : G → ℂ, IsLocallyConstant χ ∧ χ a ≠ 1 ∧ ∀ φ ∈ SB G, l (fun x => χ x * φ x) = l φ)
    (h0 : l (ind U₀ 0) = 0) {φ : G → ℂ} (hφ : φ ∈ SB G) : l φ = 0 := by sorry
