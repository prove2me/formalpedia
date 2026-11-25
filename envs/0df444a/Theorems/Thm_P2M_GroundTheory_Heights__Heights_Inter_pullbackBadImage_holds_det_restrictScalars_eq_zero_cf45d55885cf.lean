-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_pullbackBadImage_holds_det_restrictScalars_eq_zero_cf45d55885cf
-- name    : P2M_GroundTheory_Heights__Heights_Inter_pullbackBadImage_holds_det_restrictScalars_eq_zero_cf45d55885cf
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:43:09.851022+00:00
-- url     : https://prove2.me/theorems/2ce09d9f-2dc1-5a4f-b21f-c4177a0fe67d
-- title:
--   P2 M Ground Theory Heights  Heights Inter pullback Bad Image holds det restrict Scalars eq zero cf45d55885cf: P2 M Ground Theory Heights  Heights Inter pullback Bad Image holds det restrict Scalars eq
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter pullback Bad Image holds det restrict Scalars eq zero cf45d55885cf construction uses the P2 M Ground Theory Heights  Heights Inter pullback Bad Image holds det restrict Scalars eq zero cf45d55885cf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/DetRestrictScalarsEqZero.lean#L62-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/DetRestrictScalarsEqZero.lean#L62-L69

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeE
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsFurtherMore
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_DetRestrictScalarsEqZero
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
  Topology Filter
open GroundTheory.Heights₂.Heights.Inter.pullbackBadImage_holds
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
  {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {P' J' : Ideal (MRing ι')} {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_Inter_pullbackBadImage_holds_det_restrictScalars_eq_zero_cf45d55885cf {m : ℕ} (f : (Fin m → ℂ) →L[ℂ] (Fin m → ℂ))
    (h : LinearMap.det (f : (Fin m → ℂ) →ₗ[ℂ] (Fin m → ℂ)) = 0) :
    (f.restrictScalars ℝ).det = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«pullbackBadImage_holds».«det_restrictScalars_eq_zero» := P2M_GroundTheory_Heights__Heights_Inter_pullbackBadImage_holds_det_restrictScalars_eq_zero_cf45d55885cf
