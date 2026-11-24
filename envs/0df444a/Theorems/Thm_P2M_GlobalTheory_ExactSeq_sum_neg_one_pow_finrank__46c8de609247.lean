-- Prove2me | Theorems.Thm_P2M_GlobalTheory_ExactSeq_sum_neg_one_pow_finrank__46c8de609247
-- name    : P2M_GlobalTheory_ExactSeq_sum_neg_one_pow_finrank__46c8de609247
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T21:42:32.455259+00:00
-- url     : https://prove2.me/theorems/479f7950-42d1-4f97-986d-c01108cced82
-- title:
--   P2 M Global Theory Exact Seq sum neg one pow finrank  46c8de609247: P2 M Global Theory Exact Seq sum neg one pow finrank  46c8de609247
-- statement:
--   The P2 M Global Theory Exact Seq sum neg one pow finrank  46c8de609247 construction uses the P2 M Global Theory Exact Seq sum neg one pow finrank  46c8de609247 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SumNegOnePowFinrankEqZero.lean#L76-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SumNegOnePowFinrankEqZero.lean#L76-L95

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HdimEqZeroOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SumNegOnePowFinrankEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits Module
universe t v u
noncomputable section
open GlobalTheory
open GlobalTheory.ExactSeq
variable {k : Type*} [DivisionRing k]
variable {A B C : ℕ → Type*} [∀ i, AddCommGroup (A i)] [∀ i, AddCommGroup (B i)]
  [∀ i, AddCommGroup (C i)] [∀ i, Module k (A i)] [∀ i, Module k (B i)] [∀ i, Module k (C i)]
  (f : ∀ i, A i →ₗ[k] B i) (g : ∀ i, B i →ₗ[k] C i) (δ : ∀ i, C i →ₗ[k] A (i + 1))

theorem P2M_GlobalTheory_ExactSeq_sum_neg_one_pow_finrank__46c8de609247 (N : ℕ) (hA : ∀ i < N, Module.Finite k (A i))
    (hB : ∀ i < N, Module.Finite k (B i)) (hC : ∀ i < N, Module.Finite k (C i))
    (h₂ : ∀ i < N, Function.Exact (f i) (g i)) (h₃ : ∀ i < N, Function.Exact (g i) (δ i))
    (h₁ : ∀ i < N, Function.Exact (δ i) (f (i + 1))) :
    ∑ i ∈ Finset.range N, (-1 : ℤ) ^ i * (finrank k (A i) - finrank k (B i) + finrank k (C i)) =
      finrank k (LinearMap.ker (f 0)) - (-1) ^ N * finrank k (LinearMap.ker (f N)) := by sorry

alias «GlobalTheory».«ExactSeq».«sum_neg_one_pow_finrank₃» := P2M_GlobalTheory_ExactSeq_sum_neg_one_pow_finrank__46c8de609247
