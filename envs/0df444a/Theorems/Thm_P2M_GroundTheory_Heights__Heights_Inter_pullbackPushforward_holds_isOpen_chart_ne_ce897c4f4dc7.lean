-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_pullbackPushforward_holds_isOpen_chart_ne_ce897c4f4dc7
-- name    : P2M_GroundTheory_Heights__Heights_Inter_pullbackPushforward_holds_isOpen_chart_ne_ce897c4f4dc7
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:41:50.180878+00:00
-- url     : https://prove2.me/theorems/578d5b4b-be63-5f6c-8503-9fb96d8c6847
-- title:
--   P2 M Ground Theory Heights  Heights Inter pullback Pushforward holds is Open chart ne ce897c4f4dc7: P2 M Ground Theory Heights  Heights Inter pullback Pushforward holds is Open chart ne ce897c4f4dc7
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter pullback Pushforward holds is Open chart ne ce897c4f4dc7 construction uses the P2 M Ground Theory Heights  Heights Inter pullback Pushforward holds is Open chart ne ce897c4f4dc7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/HasStrictFDerivAtEquiv.lean#L145-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/HasStrictFDerivAtEquiv.lean#L145-L159

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

theorem P2M_GroundTheory_Heights__Heights_Inter_pullbackPushforward_holds_isOpen_chart_ne_ce897c4f4dc7 {f : MRing ι'} {a : K' → ℕ} (hf : IsMultiHomog f a) (j : Fin R.A.n) :
    IsOpen ((R.A.chart j).target ∩
      (R.A.chart j).symm ⁻¹' {x | eval (R.lift x x) (map (Int.castRingHom ℂ) f) ≠ 0}) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«pullbackPushforward_holds».«isOpen_chart_ne» := P2M_GroundTheory_Heights__Heights_Inter_pullbackPushforward_holds_isOpen_chart_ne_ce897c4f4dc7
