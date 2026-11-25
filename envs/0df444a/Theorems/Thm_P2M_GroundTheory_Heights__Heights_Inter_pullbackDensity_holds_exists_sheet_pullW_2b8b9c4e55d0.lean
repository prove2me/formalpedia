-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_pullbackDensity_holds_exists_sheet_pullW_2b8b9c4e55d0
-- name    : P2M_GroundTheory_Heights__Heights_Inter_pullbackDensity_holds_exists_sheet_pullW_2b8b9c4e55d0
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:42:57.873133+00:00
-- url     : https://prove2.me/theorems/c5a66ff0-4ec7-51ef-96c1-73ddb368f7c3
-- title:
--   P2 M Ground Theory Heights  Heights Inter pullback Density holds exists sheet pull W 2b8b9c4e55d0: P2 M Ground Theory Heights  Heights Inter pullback Density holds exists sheet pull W 2b8b9c4e55d0
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter pullback Density holds exists sheet pull W 2b8b9c4e55d0 construction uses the P2 M Ground Theory Heights  Heights Inter pullback Density holds exists sheet pull W 2b8b9c4e55d0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ExistsSheetPullW.lean#L35-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ExistsSheetPullW.lean#L35-L220

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridge
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PullWMemFibre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ExistsSheetPullW
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
open GroundTheory.Heights₂.Heights.Inter.pullbackDensity_holds
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
  {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {P' J' : Ideal (MRing ι')} {n : ℕ}
  (R : AnLogRes P' J' n) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))

theorem P2M_GroundTheory_Heights__Heights_Inter_pullbackDensity_holds_exists_sheet_pullW_2b8b9c4e55d0 (hv : IsBlockMap κ v) (hP : IsArithVar (imageZ v P') (n + 1))
    (L : Fin n → HermLine ι) (L' : Fin n → HermLine ι') (A : HermLine ι) (A' : HermLine ι') (s : MRing ι)
    (hL : ∀ j, IsSmoothHerm (L j)) (hLL' : ∀ j, IsPullHerm κ v (L j) (L' j)) (hAA' : IsPullHerm κ v A A')
    (hs : IsSectionOn (imageZ v P') A s) (x : R.X) (hx : x ∉ pullBad R v Ψ) :
    ∃ γ : (Fin n → ℂ) → (Σ k, ι k) → ℂ, IsSheet (imageZ v P') Ψ (pullQ R v Ψ x) (pullW R v Ψ x) γ ∧
      logNorm A s (γ (pullQ R v Ψ x)) * maDensity (fun j y' => pot L j (γ y')) (pullQ R v Ψ x) =
        logNorm A' (rename v s) (R.lift x x) * pushDens R.A (fun j => potOf R (L' j)) (pullQ R v Ψ) x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«pullbackDensity_holds».«exists_sheet_pullW» := P2M_GroundTheory_Heights__Heights_Inter_pullbackDensity_holds_exists_sheet_pullW_2b8b9c4e55d0
