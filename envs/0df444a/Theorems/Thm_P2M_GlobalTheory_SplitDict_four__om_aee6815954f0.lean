-- Prove2me | Theorems.Thm_P2M_GlobalTheory_SplitDict_four__om_aee6815954f0
-- name    : P2M_GlobalTheory_SplitDict_four__om_aee6815954f0
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T21:54:48.194239+00:00
-- url     : https://prove2.me/theorems/0dd18901-0442-4ea5-8e84-7cbff20ea93a
-- title:
--   P2 M Global Theory Split Dict four  om aee6815954f0: P2 M Global Theory Split Dict four  om aee6815954f0
-- statement:
--   The P2 M Global Theory Split Dict four  om aee6815954f0 construction uses the P2 M Global Theory Split Dict four  om aee6815954f0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsBoxInvariantSnd.lean#L325-L331
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsBoxInvariantSnd.lean#L325-L331

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

theorem P2M_GlobalTheory_SplitDict_four__om_aee6815954f0 (Φ : Matrix W (ρ ⊕ v ⊕ ρ) k → ℂ) (ν : Matrix v ρ k) (ν' : Matrix ρ v k) (b : Matrix ρ ρ k)
    (ξ : Matrix W ρ k) (η : Matrix ρ W k) (x₀ : Matrix W v k) :
    four₁ ψ m s₁ (om μ (uGL ν ν' b) 1 Φ) (ξ, η, x₀) =
      chr ψ s₁ (trace (η * (ξ * b + x₀ * ν))) * four₁ ψ m s₁ Φ (ξ, η, x₀ + ξ * ν') := by sorry

alias «GlobalTheory».«SplitDict».«four₁_om» := P2M_GlobalTheory_SplitDict_four__om_aee6815954f0
