-- Prove2me | Theorems.Thm_P2M_GlobalTheory_SplitDict_four__om_zGL_eq_chr_trace_mul_b98df81161e5
-- name    : P2M_GlobalTheory_SplitDict_four__om_zGL_eq_chr_trace_mul_b98df81161e5
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:07:36.513704+00:00
-- url     : https://prove2.me/theorems/4c9f0dc4-424b-45b3-aa39-156e0d117cc5
-- title:
--   P2 M Global Theory Split Dict four  om z GL eq chr trace mul b98df81161e5: P2 M Global Theory Split Dict four  om z GL eq chr trace mul b98df81161e5
-- statement:
--   The P2 M Global Theory Split Dict four  om z GL eq chr trace mul b98df81161e5 construction uses the P2 M Global Theory Split Dict four  om z GL eq chr trace mul b98df81161e5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsBoxInvariantSnd.lean#L358-L367
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsBoxInvariantSnd.lean#L358-L367

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

theorem P2M_GlobalTheory_SplitDict_four__om_zGL_eq_chr_trace_mul_b98df81161e5 (Φ : Matrix W (ρ ⊕ v ⊕ ρ) k → ℂ) (b : Matrix ρ ρ k)
    (ξ : Matrix W ρ k) (η : Matrix ρ W k) (x₀ : Matrix W v k) :
    four₁ ψ m s₁ (om μ (zGL v b) 1 Φ) (ξ, η, x₀) =
      chr ψ s₁ (∑ p, ∑ q, (η * ξ) p q * b q p) * four₁ ψ m s₁ Φ (ξ, η, x₀) := by sorry

alias «GlobalTheory».«SplitDict».«four₁_om_zGL_eq_chr_trace_mul» := P2M_GlobalTheory_SplitDict_four__om_zGL_eq_chr_trace_mul_b98df81161e5
