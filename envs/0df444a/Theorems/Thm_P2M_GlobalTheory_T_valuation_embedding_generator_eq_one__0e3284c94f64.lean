-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_valuation_embedding_generator_eq_one__0e3284c94f64
-- name    : P2M_GlobalTheory_T_valuation_embedding_generator_eq_one__0e3284c94f64
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:06:47.909795+00:00
-- url     : https://prove2.me/theorems/66426a30-2f5c-45dd-a7d4-930e0ba719fd
-- title:
--   P2 M Global Theory T valuation embedding generator eq one  0e3284c94f64: P2 M Global Theory T valuation embedding generator eq one  0e3284c94f64
-- statement:
--   The P2 M Global Theory T valuation embedding generator eq one  0e3284c94f64 construction uses the P2 M Global Theory T valuation embedding generator eq one  0e3284c94f64 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ValuationEmbeddingGeneratorEqOneStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ValuationEmbeddingGeneratorEqOneStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ValuationEmbeddingGeneratorEqOne
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ValuationEmbeddingGeneratorEqOneStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_valuation_embedding_generator_eq_one__0e3284c94f64 : ∀ (K : Type) [Field K] [NumberField K] (A : ValuationSubring ℂ) (p : ℕ), p.Prime → (p : ℂ) ∈ A.nonunits → ∀ (P : HeightOneSpectrum (𝓞 K)), (p : 𝓞 K) ∉ P.asIdeal → ∀ (α : 𝓞 K) (h : ℕ), Ideal.span {α} = P.asIdeal ^ h → ∀ σ : K →+* ℂ, A.valuation (σ (α : K)) = 1 := by sorry

alias «GlobalTheory».«T».«valuation_embedding_generator_eq_one'» := P2M_GlobalTheory_T_valuation_embedding_generator_eq_one__0e3284c94f64
