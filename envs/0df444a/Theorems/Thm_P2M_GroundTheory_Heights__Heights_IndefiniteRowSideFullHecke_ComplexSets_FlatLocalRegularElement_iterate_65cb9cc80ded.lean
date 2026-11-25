-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FlatLocalRegularElement_iterate_65cb9cc80ded
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FlatLocalRegularElement_iterate_65cb9cc80ded
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:19:43.932664+00:00
-- url     : https://prove2.me/theorems/e7f03748-fb58-4f14-9dbd-edbad88732ed
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Flat Local Regular Element iterate 65cb9cc80ded: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Comp
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Flat Local Regular Element iterate 65cb9cc80ded construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Flat Local Regular Element iterate 65cb9cc80ded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PFlatLocalRegularSequence.lean#L21-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PFlatLocalRegularSequence.lean#L21-L44

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFlatLocalRegularSequence
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFlatLocalRegularElement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFlatLocalRegularSequence
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
open IsLocalRing RingTheory.Sequence Pointwise

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FlatLocalRegularElement_iterate_65cb9cc80ded (h : FlatLocalRegularElement.Statement)
    {A B : Type} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] [Algebra A B]
    (hA : IsNoetherianRing A) (hB : IsNoetherianRing B) (hl : IsLocalHom (algebraMap A B))
    (ys : List B) (hys : ∀ y ∈ ys, y ∈ maximalIdeal B)
    (M : Type) [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
    (hfin : Module.Finite B M) (hflat : Module.Flat A M)
    (hreg : IsWeaklyRegular (M ⧸ ((maximalIdeal A).map (algebraMap A B) • (⊤ : Submodule B M))) ys) :
    IsWeaklyRegular M ys ∧ Module.Flat A (M ⧸ (Ideal.ofList ys • (⊤ : Submodule B M))) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«FlatLocalRegularElement».«iterate» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FlatLocalRegularElement_iterate_65cb9cc80ded
