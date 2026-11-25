-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_primeFibreLocalRing_nonempty_equiv_of_surjective_56cf03546f44
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_primeFibreLocalRing_nonempty_equiv_of_surjective_56cf03546f44
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:21:47.183813+00:00
-- url     : https://prove2.me/theorems/0ada6796-aff3-4f64-83fa-ce2ce0fadb97
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets prime Fibre Local Ring nonempty equiv of surjective 56cf03546f44: P2 M Ground Theory Heights  Heights Indefinite Row Sid
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets prime Fibre Local Ring nonempty equiv of surjective 56cf03546f44 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets prime Fibre Local Ring nonempty equiv of surjective 56cf03546f44 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PFormalFibreQuotient.lean#L7-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PFormalFibreQuotient.lean#L7-L66

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFormalFibreQuotient
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFormalFibreQuotient
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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_primeFibreLocalRing_nonempty_equiv_of_surjective_56cf03546f44
    {R S R' S' : Type*} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    [Algebra R R'] [Algebra S S'] (f : R →+* S) (φ : R' →+* S')
    (hf : Function.Surjective f) (hφ : Function.Surjective φ)
    (hcomm : φ.comp (algebraMap R R') = (algebraMap S S').comp f)
    (hker : RingHom.ker φ ≤ (RingHom.ker f).map (algebraMap R R'))
    (P : Ideal S') [P.IsPrime] :
    Nonempty (primeFibreLocalRing S P ≃+* primeFibreLocalRing R (P.comap φ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«primeFibreLocalRing_nonempty_equiv_of_surjective» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_primeFibreLocalRing_nonempty_equiv_of_surjective_56cf03546f44
