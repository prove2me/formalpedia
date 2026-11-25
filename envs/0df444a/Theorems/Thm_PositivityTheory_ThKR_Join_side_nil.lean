-- Prove2me | Theorems.Thm_PositivityTheory_ThKR_Join_side_nil
-- name    : PositivityTheory.ThKR.Join.side_nil
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T14:09:27.526975+00:00
-- url     : https://prove2.me/theorems/1db8c32a-63c6-5d86-9917-5f60c4dc99a6
-- title:
--   Join: side nil
-- statement:
--   The Join construction uses the side nil property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/LocalPoly.lean#L147-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/LocalPoly.lean#L147-L176

import Definitions.Def_Development_WeilBound_ThetaLifts_CartanFactorisation_ExistsGreatestProperInvariantSubmoduleOfSide
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_LocalPoly
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
open PositivityTheory PositivityTheory.ThKR PositivityTheory.ThKR.Join
open PositivityTheory.KReal PositivityTheory.ThKF.Unit
variable {r s : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

theorem PositivityTheory.ThKR.Join.side_nil {La : Ix r s → ℚ} {act : Mat r s →ₗ[ℂ] Module.End ℂ M} (h : Side La M act) :
    ∃ v : M, ∀ K : Submodule ℂ M, K ≠ ⊤ → (∀ W, ∀ x ∈ K, act W x ∈ K) → ∀ t : List M, (∀ x ∈ t, x ∈ K) → ∀ y,
      ∃ u ∈ Algebra.adjoin ℂ (Set.range act), u v = y ∧ ∀ x ∈ t, u x = 0 := by sorry
