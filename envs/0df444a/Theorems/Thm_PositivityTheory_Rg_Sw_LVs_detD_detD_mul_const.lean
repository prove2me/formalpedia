-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_detD_detD_mul_const
-- name    : PositivityTheory.Rg.Sw.LVs.detD_detD_mul_const
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:00:22.400083+00:00
-- url     : https://prove2.me/theorems/ff5fe34e-42f1-4b01-a1a4-b4b724f59103
-- title:
--   LVs: det D det D mul const
-- statement:
--   The LVs construction uses the det D det D mul const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/IteratedFDerivMulConstOf.lean#L171-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/IteratedFDerivMulConstOf.lean#L171-L181

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ContinuousOnIteratedFDerivTranslate
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_IteratedFDerivMulConstOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
open PositivityTheory.Rg.Sw
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.LVs.detD_detD_mul_const {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (F : M2 n → ℂ) (U : Set (M2 n)) (hU : IsOpen U) (hF : ContDiffOn ℂ ∞ F U) (x₀ : M2 n) (hx : x₀ ∈ U)
    (LA : Matrix ιA ιA ℂ →L[ℂ] M2 n) (LB : Matrix ιB ιB ℂ →L[ℂ] M2 n) (c : ℂ) :
    detD (fun T : Matrix ιA ιA ℂ => detD (fun S : Matrix ιB ιB ℂ => F (x₀ + LA T + LB S) * c)) =
      detD (fun T : Matrix ιA ιA ℂ => detD (fun S : Matrix ιB ιB ℂ => F (x₀ + LA T + LB S))) * c := by sorry
