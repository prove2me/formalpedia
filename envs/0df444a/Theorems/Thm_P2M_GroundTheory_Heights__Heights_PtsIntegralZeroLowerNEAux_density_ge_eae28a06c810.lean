-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsIntegralZeroLowerNEAux_density_ge_eae28a06c810
-- name    : P2M_GroundTheory_Heights__Heights_PtsIntegralZeroLowerNEAux_density_ge_eae28a06c810
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:16:16.543322+00:00
-- url     : https://prove2.me/theorems/6c90b3e6-7d11-4f37-a9e0-667cb6136eb6
-- title:
--   P2 M Ground Theory Heights  Heights Pts Integral Zero Lower NEAux density ge eae28a06c810: P2 M Ground Theory Heights  Heights Pts Integral Zero Lower NEAux density ge eae28a06c810
-- statement:
--   The P2 M Ground Theory Heights  Heights Pts Integral Zero Lower NEAux density ge eae28a06c810 construction uses the P2 M Ground Theory Heights  Heights Pts Integral Zero Lower NEAux density ge eae28a06c810 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PPtsIntegralZeroLowerNE.lean#L126-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PPtsIntegralZeroLowerNE.lean#L126-L137

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeightNE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PPtsIntegralZeroLowerNE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial MeasureTheory
noncomputable section
open GroundTheory.Heights₂.Heights.PtsIntegralZeroLowerNEAux
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
omit [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_PtsIntegralZeroLowerNEAux_density_ge_eae28a06c810 {W : Ideal (MRing ι)} {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (0 + 1) → ℂ)}
    {φ : Fin 0 → ((Σ k, ι k) → ℂ) → ℝ} {g : ((Σ k, ι k) → ℂ) → ℝ} {c : ℝ}
    (hc : ∀ z ∈ mcPts W, c ≤ g z) {y : Fin 0 → ℂ} {w : ((k : K) → ι k) → ℂ} (hw : w ∈ fibre W Ψ y) :
    c ≤ sheetDensity W Ψ φ g y w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PtsIntegralZeroLowerNEAux».«density_ge» := P2M_GroundTheory_Heights__Heights_PtsIntegralZeroLowerNEAux_density_ge_eae28a06c810
