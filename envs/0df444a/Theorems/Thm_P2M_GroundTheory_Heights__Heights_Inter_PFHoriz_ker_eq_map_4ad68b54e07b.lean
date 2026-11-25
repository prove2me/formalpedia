-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PFHoriz_ker_eq_map_4ad68b54e07b
-- name    : P2M_GroundTheory_Heights__Heights_Inter_PFHoriz_ker_eq_map_4ad68b54e07b
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:42:40.313092+00:00
-- url     : https://prove2.me/theorems/30086695-a86b-435d-8d0e-0ab896a486e3
-- title:
--   P2 M Ground Theory Heights  Heights Inter PFHoriz ker eq map 4ad68b54e07b: P2 M Ground Theory Heights  Heights Inter PFHoriz ker eq map 4ad68b54e07b
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter PFHoriz ker eq map 4ad68b54e07b construction uses the P2 M Ground Theory Heights  Heights Inter PFHoriz ker eq map 4ad68b54e07b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PPFHoriz.lean#L140-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PPFHoriz.lean#L140-L157

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsPFHoriz
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFHoriz
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.PFHoriz
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
  {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {P' : Ideal (MRing ι')}

theorem P2M_GroundTheory_Heights__Heights_Inter_PFHoriz_ker_eq_map_4ad68b54e07b {σ τ Φ Φ' : Type} [Field Φ] [Field Φ'] [Algebra Φ Φ']
    (β : MvPolynomial τ ℤ →+* MvPolynomial σ Φ) (y : σ → Φ') (φ : MvPolynomial τ ℤ →+* Φ')
    (W : Ideal (MvPolynomial τ ℤ)) (hφ : RingHom.ker φ = W) (hcomp : ∀ F, aeval y (β F) = φ F)
    (hclear : ∀ g, ∃ c : Φ, c ≠ 0 ∧ ∃ F, C c * g = β F) :
    RingHom.ker (aeval y : MvPolynomial σ Φ →ₐ[Φ] Φ') = Ideal.map β W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«PFHoriz».«ker_eq_map» := P2M_GroundTheory_Heights__Heights_Inter_PFHoriz_ker_eq_map_4ad68b54e07b
