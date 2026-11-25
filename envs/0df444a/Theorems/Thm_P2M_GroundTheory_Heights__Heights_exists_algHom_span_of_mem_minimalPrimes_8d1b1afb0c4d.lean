-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_algHom_span_of_mem_minimalPrimes_8d1b1afb0c4d
-- name    : P2M_GroundTheory_Heights__Heights_exists_algHom_span_of_mem_minimalPrimes_8d1b1afb0c4d
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:09:15.03367+00:00
-- url     : https://prove2.me/theorems/0d010fac-235e-5c66-8734-25aabc0fb725
-- title:
--   P2 M Ground Theory Heights  Heights exists alg Hom span of mem minimal Primes 8d1b1afb0c4d: P2 M Ground Theory Heights  Heights exists alg Hom span of mem minimal Primes 8d1b1afb0c4d
-- statement:
--   The P2 M Ground Theory Heights  Heights exists alg Hom span of mem minimal Primes 8d1b1afb0c4d construction uses the P2 M Ground Theory Heights  Heights exists alg Hom span of mem minimal Primes 8d1b1afb0c4d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/CurveNormalisationFiniteLemmas.lean#L58-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/CurveNormalisationFiniteLemmas.lean#L58-L75

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveNormalisationLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_LocalIntegralClosureChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_CurveNormalisationFiniteLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial ComplexSets FieldNumbers
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_exists_algHom_span_of_mem_minimalPrimes_8d1b1afb0c4d (hN : NoetherIntegralClosureFinite.Statement.{0}) {n : ℕ}
    {O : Type} [CommRing O] (φ : MvPolynomial (Fin n) ℂ →+* O)
    (hφ : ∀ o : O, ∃ f s, IsUnit (φ s) ∧ o * φ s = φ f) {p : Ideal O} (hp : p ∈ minimalPrimes O) :
    ∃ g : FractionRing O →ₐ[O] FractionRing (O ⧸ p), ∃ t : Finset (FractionRing (O ⧸ p)),
      ∀ x : FractionRing O, IsIntegral O x → g x ∈ Submodule.span O (t : Set (FractionRing (O ⧸ p))) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«exists_algHom_span_of_mem_minimalPrimes» := P2M_GroundTheory_Heights__Heights_exists_algHom_span_of_mem_minimalPrimes_8d1b1afb0c4d
