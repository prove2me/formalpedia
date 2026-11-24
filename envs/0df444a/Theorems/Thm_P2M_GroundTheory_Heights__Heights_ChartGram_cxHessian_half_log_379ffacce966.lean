-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartGram_cxHessian_half_log_379ffacce966
-- name    : P2M_GroundTheory_Heights__Heights_ChartGram_cxHessian_half_log_379ffacce966
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:11:16.292934+00:00
-- url     : https://prove2.me/theorems/69913cd0-4b72-439d-ba8e-8bfa659b4c0b
-- title:
--   P2 M Ground Theory Heights  Heights Chart Gram cx Hessian half log 379ffacce966: P2 M Ground Theory Heights  Heights Chart Gram cx Hessian half log 379ffacce966
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Gram cx Hessian half log 379ffacce966 construction uses the P2 M Ground Theory Heights  Heights Chart Gram cx Hessian half log 379ffacce966 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ChartGramHess.lean#L90-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ChartGramHess.lean#L90-L112

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ChartGramHess
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open scoped InnerProductSpace
open Filter Topology
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
open ReciprocityTheory.ChartRestriction.G.Geo (cxHessian)

theorem P2M_GroundTheory_Heights__Heights_ChartGram_cxHessian_half_log_379ffacce966 [CompleteSpace F] {D : ℕ} {u : (Fin D → ℂ) → F}
    {y : Fin D → ℂ} (hu : ∀ᶠ y' in 𝓝 y, AnalyticAt ℂ u y') (h0 : u y ≠ 0) (i j : Fin D) :
    cxHessian (fun y' => 2⁻¹ * Real.log (⟪u y', u y'⟫_ℂ).re) y i j =
      (⟪u y, u y⟫_ℂ * ⟪fderiv ℂ u y (Pi.single j 1), fderiv ℂ u y (Pi.single i 1)⟫_ℂ -
          ⟪u y, fderiv ℂ u y (Pi.single i 1)⟫_ℂ * ⟪fderiv ℂ u y (Pi.single j 1), u y⟫_ℂ) /
        (2 * ⟪u y, u y⟫_ℂ ^ 2) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartGram».«cxHessian_half_log» := P2M_GroundTheory_Heights__Heights_ChartGram_cxHessian_half_log_379ffacce966
