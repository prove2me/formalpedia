-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_primitive_with_resultant_denominator_cfd22a00b3ce
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_primitive_with_resultant_denominator_cfd22a00b3ce
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:21:27.768585+00:00
-- url     : https://prove2.me/theorems/4f35c9b9-904a-4cb9-8ac9-777a45b3feaf
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets primitive with resultant denominator cfd22a00b3ce: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Co
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets primitive with resultant denominator cfd22a00b3ce construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets primitive with resultant denominator cfd22a00b3ce property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PIrreducibleGermPrimitiveForm.lean#L14-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PIrreducibleGermPrimitiveForm.lean#L14-L90

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIrreducibleGermPrimitiveForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteFibreGermIntegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StZariskiAnalyticNormality
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDiscrAdjoin
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PIrreducibleGermPrimitiveForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology Filter Polynomial
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_primitive_with_resultant_denominator_cfd22a00b3ce (hG : GroundTheory.Heights₂.Heights.ComplexSets.GenericPrimitive.Statement)
    (hD : GroundTheory.Heights₂.Heights.ComplexSets.DiscrAdjoin.Statement)
    {R S : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [CommRing S] [IsDomain S] [Algebra R S]
    (hinj : Function.Injective (algebraMap R S)) [Algebra.IsIntegral R S] (c : ℂ →+* R)
    {n : ℕ} (z : Fin n → S) :
    ∃ (cc : Fin n → ℂ) (p : R[X]), p.Monic ∧ 0 < p.natDegree ∧
      aeval (∑ j, algebraMap R S (c (cc j)) * z j) p = 0 ∧
      p.resultant (derivative p) p.natDegree (p.natDegree - 1) ≠ 0 ∧
      ∀ i, ∃ f : R[X], f.natDegree < p.natDegree ∧
        aeval (∑ j, algebraMap R S (c (cc j)) * z j) f =
          algebraMap R S (p.resultant (derivative p) p.natDegree (p.natDegree - 1)) * z i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«primitive_with_resultant_denominator» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_primitive_with_resultant_denominator_cfd22a00b3ce
