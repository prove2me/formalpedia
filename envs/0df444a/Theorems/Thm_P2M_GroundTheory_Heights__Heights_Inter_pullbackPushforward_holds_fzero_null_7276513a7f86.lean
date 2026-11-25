-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_pullbackPushforward_holds_fzero_null_7276513a7f86
-- name    : P2M_GroundTheory_Heights__Heights_Inter_pullbackPushforward_holds_fzero_null_7276513a7f86
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:41:48.137028+00:00
-- url     : https://prove2.me/theorems/9771dc5f-e18b-547b-ab71-bfe8aa459307
-- title:
--   P2 M Ground Theory Heights  Heights Inter pullback Pushforward holds fzero null 7276513a7f86: P2 M Ground Theory Heights  Heights Inter pullback Pushforward holds fzero null 7276513a7f86
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter pullback Pushforward holds fzero null 7276513a7f86 construction uses the P2 M Ground Theory Heights  Heights Inter pullback Pushforward holds fzero null 7276513a7f86 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/HasStrictFDerivAtEquiv.lean#L161-L244
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/HasStrictFDerivAtEquiv.lean#L161-L244

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridge
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PullWMemFibre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PullBad
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_HasStrictFDerivAtEquiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M
  Topology Filter Set
open GroundTheory.Heights₂.Heights.Inter.pullbackPushforward_holds
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
  {P' J' : Ideal (MRing ι')} {n : ℕ} (R : AnLogRes P' J' n) {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')}

theorem P2M_GroundTheory_Heights__Heights_Inter_pullbackPushforward_holds_fzero_null_7276513a7f86 (hP' : IsArithVar P' (n + 1)) {f : MRing ι'} {a : K' → ℕ} (hf : IsMultiHomog f a)
    (hfP : f ∉ P') (j : Fin R.A.n) :
    volume ((R.A.chart j).target ∩
      (R.A.chart j).symm ⁻¹' {x | eval (R.lift x x) (map (Int.castRingHom ℂ) f) = 0}) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«pullbackPushforward_holds».«fzero_null» := P2M_GroundTheory_Heights__Heights_Inter_pullbackPushforward_holds_fzero_null_7276513a7f86
