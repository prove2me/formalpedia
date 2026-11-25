-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_spherical_detD
-- name    : PositivityTheory.Rg.Sw.LVs.spherical_detD
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:01:08.442154+00:00
-- url     : https://prove2.me/theorems/8a970677-ee28-4575-84fe-6b0c6ffa55eb
-- title:
--   LVs: spherical det D
-- statement:
--   The LVs construction uses the spherical det D property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/IntegrableIteratedFDerivTranslate.lean#L30-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/IntegrableIteratedFDerivTranslate.lean#L30-L81

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_IteratedFDerivMulConstOf
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_IntegrableIteratedFDerivTranslate
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

theorem PositivityTheory.Rg.Sw.LVs.spherical_detD (hHI : HolInt) (F : M2 n → ℂ) (hF : ContDiffOn ℂ ∞ F (Dom n))
    {Kg : Type} [TopologicalSpace Kg] [CompactSpace Kg] [MeasurableSpace Kg] [BorelSpace Kg]
    (μ : Measure Kg) [IsFiniteMeasure μ] [IsFiniteMeasureOnCompacts μ] (ι : Kg → M2 n) (hι : Continuous ι)
    (c : Kg → ℂ) (hc : Continuous c)
    {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (LA : M2 n → Matrix ιA ιA ℂ →L[ℂ] M2 n) (LB : M2 n → Matrix ιB ιB ℂ →L[ℂ] M2 n)
    (hLA : ∀ M x T, LA (M * x) T = M * LA x T) (hLB : ∀ M x S, LB (M * x) S = M * LB x S)
    (g : M2 n) (hg : ∀ k, ι k * g ∈ Dom n) :
    detD (fun T : Matrix ιA ιA ℂ => detD (fun S : Matrix ιB ιB ℂ =>
        ∫ k, F (ι k * (g + LA g T + LB g S)) * c k ∂μ)) =
      ∫ k, detD (fun T : Matrix ιA ιA ℂ => detD (fun S : Matrix ιB ιB ℂ =>
        F (ι k * g + LA (ι k * g) T + LB (ι k * g) S))) * c k ∂μ := by sorry
