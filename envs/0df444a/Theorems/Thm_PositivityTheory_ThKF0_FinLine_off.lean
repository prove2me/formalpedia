-- Prove2me | Theorems.Thm_PositivityTheory_ThKF0_FinLine_off
-- name    : PositivityTheory.ThKF0.FinLine.off
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T09:04:10.756643+00:00
-- url     : https://prove2.me/theorems/ff960811-7ac4-5726-8da6-3f9d2d0df4df
-- title:
--   Fin Line: off
-- statement:
--   The Fin Line construction uses the off property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/LagrangianUniqueness/Imports.lean#L70-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/LagrangianUniqueness/Imports.lean#L70-L104

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

theorem PositivityTheory.ThKF0.FinLine.off (h2 : ∀ a ∉ P, ∃ χ : G → ℂ, IsLocallyConstant χ ∧ χ a ≠ 1 ∧ ∀ φ ∈ SB G, l (fun x => χ x * φ x) = l φ)
    {φ : G → ℂ} (hφ : φ ∈ SB G) (hP : ∀ a, φ a ≠ 0 → a ∉ P) : l φ = 0 := by sorry
