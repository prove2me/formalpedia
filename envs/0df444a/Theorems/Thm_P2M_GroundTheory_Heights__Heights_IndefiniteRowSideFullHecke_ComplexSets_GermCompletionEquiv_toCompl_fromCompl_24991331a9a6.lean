-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_GermCompletionEquiv_toCompl_fromCompl_24991331a9a6
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_GermCompletionEquiv_toCompl_fromCompl_24991331a9a6
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:19:48.865252+00:00
-- url     : https://prove2.me/theorems/cd27eba1-d127-5aa9-99c2-7fcead337c7d
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Germ Completion Equiv to Compl from Compl 24991331a9a6: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hec
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Germ Completion Equiv to Compl from Compl 24991331a9a6 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Germ Completion Equiv to Compl from Compl 24991331a9a6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGermCompletionEquiv.lean#L221-L225
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGermCompletionEquiv.lean#L221-L225

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGermCompletionEquiv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHolGermPointIdealSpan
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPolyGermPointPow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGermCompletionEquiv
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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.GermCompletionEquiv
variable {σ : Type} [Fintype σ] (w : σ → ℂ)
variable (I : Ideal (MvPolynomial σ ℂ))
variable (hH : HolGermPointIdealSpan.Statement) (hP : PolyGermPointPow.Statement)

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_GermCompletionEquiv_toCompl_fromCompl_24991331a9a6 (x : AdicCompletion (germQuotPointIdeal I w) (holGerms w ⧸ I.map (polyGerm w))) :
    toCompl w I (fromCompl w I hH hP x) = x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«GermCompletionEquiv».«toCompl_fromCompl» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_GermCompletionEquiv_toCompl_fromCompl_24991331a9a6
