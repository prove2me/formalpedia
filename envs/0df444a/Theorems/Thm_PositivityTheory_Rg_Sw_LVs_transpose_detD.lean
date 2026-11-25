-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_transpose_detD
-- name    : PositivityTheory.Rg.Sw.LVs.transpose_detD
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T18:01:13.404794+00:00
-- url     : https://prove2.me/theorems/a4ef3f5e-8359-4c94-8970-5c1f8d84899e
-- title:
--   LVs: transpose det D
-- statement:
--   The LVs construction uses the transpose det D property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/IntegrableIteratedFDerivTranslate.lean#L83-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/IntegrableIteratedFDerivTranslate.lean#L83-L173

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

theorem PositivityTheory.Rg.Sw.LVs.transpose_detD (hI : InfInv) (F1 F2 : M2 n → ℂ) (χ1 χ2 : M2 n → ℂ) (hF1 : ContDiffOn ℂ ∞ F1 (Dom n))
    (hF2 : ContDiffOn ℂ ∞ F2 (Dom n)) (h1 : ∀ P x, InP P → x ∈ Dom n → F1 (P * x) = χ1 P * F1 x)
    (h2 : ∀ P x, InP P → x ∈ Dom n → F2 (P * x) = χ2 P * F2 x)
    (h12 : ∀ P, InP P → χ1 P * χ2 P = ((‖(P.toBlocks₂₂).det‖ ^ (-(2 * (n : ℤ))) : ℝ) : ℂ))
    (Kg : Type) [Group Kg] [TopologicalSpace Kg] [IsTopologicalGroup Kg] [CompactSpace Kg] [MeasurableSpace Kg]
    [BorelSpace Kg] (μ : Measure Kg) [μ.IsHaarMeasure] (ι : Kg →* M2 n) (hι : Continuous ι)
    (hK : ∀ g, InK g ↔ ∃ k, ι k = g)
    {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (WA : Matrix ιA ιA ℂ →L[ℂ] M2 n) (WB : Matrix ιB ιB ℂ →L[ℂ] M2 n)
    (hW : ∀ (T T' : Matrix ιA ιA ℂ) (S S' : Matrix ιB ιB ℂ), (WA T + WB S) * (WA T' + WB S') = 0) :
    ∫ k, detD (fun T : Matrix ιA ιA ℂ => detD (fun S : Matrix ιB ιB ℂ =>
        F1 (ι k + ι k * WA T + ι k * WB S))) * F2 (ι k) ∂μ =
      (-1) ^ (Fintype.card ιA + Fintype.card ιB) * ∫ k, F1 (ι k) * detD (fun T : Matrix ιA ιA ℂ =>
        detD (fun S : Matrix ιB ιB ℂ => F2 (ι k + ι k * WA T + ι k * WB S))) ∂μ := by sorry
