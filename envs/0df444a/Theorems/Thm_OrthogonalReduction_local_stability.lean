-- Prove2me | Theorems.Thm_OrthogonalReduction_local_stability
-- name    : OrthogonalReduction.local_stability
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:14:20.829902+00:00
-- url     : https://prove2.me/theorems/a422d980-464c-484a-91cc-971f5638c357
-- title:
--   Orthogonal Reduction: local stability
-- statement:
--   The Orthogonal Reduction construction uses the local stability property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/OrthogonalReduction/OrthogonalReduction.lean#L125-L255
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/OrthogonalReduction/OrthogonalReduction.lean#L125-L255

module
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite_ImportedAnalyticInputs
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_OrthogonalReduction_OrthogonalReduction
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open scoped BigOperators ENNReal
open Complex MeasureTheory Real
open OrthogonalReduction
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {Ω : Type*} [MeasurableSpace Ω]
variable (μ : MeasureTheory.Measure Ω)
variable [MeasureTheory.SigmaFinite μ]
omit [CompleteSpace H] [SigmaFinite μ]

theorem OrthogonalReduction.local_stability
    (ι : H →ₗᵢ[ℂ] MeasureTheory.Lp ℂ 2 μ)
    (f0 : H) (hf0 : ‖ι f0‖ = 1)
    (M : ℝ)
    (hMpos : 0 < M)
    (hM : ∀ g : H,
      inner ℂ g f0 = 0 →
      ‖g‖ ≤ M *
        MeasureTheory.lpNorm
            (fun x : Ω => ‖(ι (g + f0) : Ω → ℂ) x‖ - ‖(ι f0 : Ω → ℂ) x‖)
            2 μ) :
    ∃ δ > 0, ∃ M' > 0, ∀ h : H,
      ‖h‖ ≤ δ →
      Complex.im (inner ℂ h f0) = 0 →
      ‖h‖ ≤ M' *
        MeasureTheory.lpNorm (fun x : Ω => ‖(ι (h + f0) : Ω → ℂ) x‖ - ‖(ι f0 : Ω → ℂ) x‖) 2 μ := by sorry
