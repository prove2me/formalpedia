-- Prove2me | Theorems.Thm_P2M_GlobalTheory_SplitDict_four__n_ee85c8071ce4
-- name    : P2M_GlobalTheory_SplitDict_four__n_ee85c8071ce4
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:07:25.578516+00:00
-- url     : https://prove2.me/theorems/1d23ee17-e188-4c31-ba54-cbe59de214ac
-- title:
--   P2 M Global Theory Split Dict four  n ee85c8071ce4: P2 M Global Theory Split Dict four  n ee85c8071ce4
-- statement:
--   The P2 M Global Theory Split Dict four  n ee85c8071ce4 construction uses the P2 M Global Theory Split Dict four  n ee85c8071ce4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsBoxInvariantSnd.lean#L347-L356
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsBoxInvariantSnd.lean#L347-L356

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_GL2CharacterZeros
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsBoxInvariantSnd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi GlobalTheory.IndefiniteRowSideFullHecke.GLMatrixJoining
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.SplitDict
variable {k : Type} [Field k]
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]
variable (ψ : AddChar k Circle) (m : Measure k) [m.IsAddHaarMeasure] (μ : kˣ →* ℂˣ) (s₁ s₂ : ℤˣ)
variable {ρ v τ w W : Type} [Fintype ρ] [DecidableEq ρ] [Fintype v] [DecidableEq v]
  [Fintype τ] [DecidableEq τ] [Fintype w] [DecidableEq w] [Fintype W] [DecidableEq W]

theorem P2M_GlobalTheory_SplitDict_four__n_ee85c8071ce4 (Φ : Matrix (τ ⊕ w ⊕ τ) (ρ ⊕ v ⊕ ρ) k → ℂ) (ν : Matrix v ρ k) (ν' : Matrix ρ v k)
    (ξ' : Matrix τ ρ k) (ξ₀ : Matrix w ρ k) (η₀ : Matrix ρ w k) (ηd : Matrix ρ τ k)
    (r ys : Matrix τ v k) (x₀₀ : Matrix w v k) :
    four₁ ψ m s₁ (om μ (nGL ν ν') 1 Φ) (glueRows ξ' ξ₀ 0, glueFun 0 η₀ ηd, glueRows r x₀₀ ys) =
      chr ψ s₁ (trace ((η₀ * x₀₀ + ηd * ys) * ν)) *
        four₁ ψ m s₁ Φ (glueRows ξ' ξ₀ 0, glueFun 0 η₀ ηd, glueRows (r + ξ' * ν') (x₀₀ + ξ₀ * ν') ys) := by sorry

alias «GlobalTheory».«SplitDict».«four₁_n» := P2M_GlobalTheory_SplitDict_four__n_ee85c8071ce4
