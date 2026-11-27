-- Prove2me | Theorems.Thm_UpperTheory_fourierSum_block_transpose_inv_eq
-- name    : UpperTheory.fourierSum_block_transpose_inv_eq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T14:50:17.40794+00:00
-- url     : https://prove2.me/theorems/e99c8e12-189d-42c7-9362-e1db0aaade70
-- title:
--   Upper Theory: fourier Sum block transpose inv eq
-- statement:
--   The Upper Theory construction uses the fourier Sum block transpose inv eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/DivisorFrames/FourierSumBlockTransposeInvEq.lean#L81-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/DivisorFrames/FourierSumBlockTransposeInvEq.lean#L81-L183

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ScaledIntegerPeriodic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemMatLatSmulBlockLat
import Definitions.Def_Development_AutomorphicArithmetic_DivisorFrames_FourierSumBlockTransposeInvEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip
open scoped Pointwise
open UpperTheory.FourierBlockTranspose

theorem UpperTheory.fourierSum_block_transpose_inv_eq :
    ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {A D₁ D₂ : Type} [Fintype A] [DecidableEq A] [Fintype D₁] [DecidableEq D₁] [Fintype D₂] [DecidableEq D₂] (ψ : AddChar k Circle) (ϖ : kˣ) (e : ℕ), IsUnif ϖ → HasConductor ψ 1 → ∀ Φ : Matrix A (D₁ ⊕ D₂) k → ℂ, IsNatDatum ϖ e Φ → ∀ u ∈ KO k A, ∀ Y : Matrix A (D₁ ⊕ D₂) k, fourierSum ψ ϖ e (Assignment.one.block D₁ D₂) (fun Z => Φ (fromCols (u.valᵀ * Z.toCols₁) ((u⁻¹).val * Z.toCols₂))) Y = fourierSum ψ ϖ e (Assignment.one.block D₁ D₂) Φ ((u⁻¹).val * Y) := by sorry
