-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_GermCompletionEquiv_fromCompl_toCompl_e9d2f81547ac
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_GermCompletionEquiv_fromCompl_toCompl_e9d2f81547ac
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:20:48.125161+00:00
-- url     : https://prove2.me/theorems/aed5c1bc-1512-4e61-8fe0-6ac0b24bc762
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Germ Completion Equiv from Compl to Compl e9d2f81547ac: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hec
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Germ Completion Equiv from Compl to Compl e9d2f81547ac construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Germ Completion Equiv from Compl to Compl e9d2f81547ac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGermCompletionEquiv.lean#L215-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGermCompletionEquiv.lean#L215-L219

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_GermCompletionEquiv_fromCompl_toCompl_e9d2f81547ac (x : AdicCompletion (polyPointIdeal I w) (MvPolynomial σ ℂ ⧸ I)) :
    fromCompl w I hH hP (toCompl w I x) = x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«GermCompletionEquiv».«fromCompl_toCompl» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_GermCompletionEquiv_fromCompl_toCompl_e9d2f81547ac
