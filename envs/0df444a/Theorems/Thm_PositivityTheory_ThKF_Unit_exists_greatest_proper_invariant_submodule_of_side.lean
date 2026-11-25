-- Prove2me | Theorems.Thm_PositivityTheory_ThKF_Unit_exists_greatest_proper_invariant_submodule_of_side
-- name    : PositivityTheory.ThKF.Unit.exists_greatest_proper_invariant_submodule_of_side
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:48:51.664132+00:00
-- url     : https://prove2.me/theorems/b2d09923-854a-5a1a-b8fd-444ff470ae32
-- title:
--   Unit: exists greatest proper invariant submodule of side
-- statement:
--   The Unit construction uses the exists greatest proper invariant submodule of side property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/CartanFactorisation/ExistsGreatestProperInvariantSubmoduleOfSide.lean#L115-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/CartanFactorisation/ExistsGreatestProperInvariantSubmoduleOfSide.lean#L115-L150

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreLM
import Definitions.Def_Development_WeilBound_ThetaLifts_CartanFactorisation_ExistsGreatestProperInvariantSubmoduleOfSide
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace
open PositivityTheory PositivityTheory.ThKF PositivityTheory.ThKF.Unit
open PositivityTheory.KReal
variable {r s : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

theorem PositivityTheory.ThKF.Unit.exists_greatest_proper_invariant_submodule_of_side {La : Ix r s → ℚ} {act : Mat r s →ₗ[ℂ] Module.End ℂ M} (h : Side La M act) :
    ∃ K : Submodule ℂ M, K ≠ ⊤ ∧ (∀ W, ∀ x ∈ K, act W x ∈ K) ∧ (∀ N, (∀ W, ∀ x ∈ N, act W x ∈ N) → N ≠ ⊤ → N ≤ K) ∧
      ∀ β : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ, (∀ a b x y, β (act (Eab a b) x) y = epsB a b * β x (act (Eab b a) y)) → ∀ x ∈ K, β x = 0 := by sorry
