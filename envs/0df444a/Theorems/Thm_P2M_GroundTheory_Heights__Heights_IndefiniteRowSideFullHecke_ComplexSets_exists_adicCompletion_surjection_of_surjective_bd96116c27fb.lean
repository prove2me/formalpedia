-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_exists_adicCompletion_surjection_of_surjective_bd96116c27fb
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_exists_adicCompletion_surjection_of_surjective_bd96116c27fb
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:21:17.635898+00:00
-- url     : https://prove2.me/theorems/9d10c3e7-b18b-4b91-8418-4412f26e818e
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets exists adic Completion surjection of surjective bd96116c27fb: P2 M Ground Theory Heights  Heights Indefinite Row Side Fu
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets exists adic Completion surjection of surjective bd96116c27fb construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets exists adic Completion surjection of surjective bd96116c27fb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PFormalFibreQuotient.lean#L68-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PFormalFibreQuotient.lean#L68-L161

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_exists_adicCompletion_surjection_of_surjective_bd96116c27fb
    {B A : Type} [CommRing B] [CommRing A] (f : B →+* A) (hf : Function.Surjective f)
    (hB : IsNoetherianRing B) (m : Ideal A) :
    ∃ φ : AdicCompletion (m.comap f) B →+* AdicCompletion m A, Function.Surjective φ ∧
      φ.comp (algebraMap B (AdicCompletion (m.comap f) B)) =
        (algebraMap A (AdicCompletion m A)).comp f ∧
      RingHom.ker φ ≤ (RingHom.ker f).map (algebraMap B (AdicCompletion (m.comap f) B)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«exists_adicCompletion_surjection_of_surjective» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_exists_adicCompletion_surjection_of_surjective_bd96116c27fb
