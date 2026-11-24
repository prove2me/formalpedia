-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_GermCompletionEquiv_eval__toCompl_657f71a1fe27
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_GermCompletionEquiv_eval__toCompl_657f71a1fe27
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:13:58.24554+00:00
-- url     : https://prove2.me/theorems/6b01ecae-7907-47b6-baa0-fd912315b834
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Germ Completion Equiv eval  to Compl 657f71a1fe27: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Co
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Germ Completion Equiv eval  to Compl 657f71a1fe27 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Germ Completion Equiv eval  to Compl 657f71a1fe27 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGermCompletionEquiv.lean#L182-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGermCompletionEquiv.lean#L182-L186

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_GermCompletionEquiv_eval__toCompl_657f71a1fe27 (k : ℕ) (x : AdicCompletion (polyPointIdeal I w) (MvPolynomial σ ℂ ⧸ I)) :
    AdicCompletion.evalₐ (germQuotPointIdeal I w) k (toCompl w I x) =
      psi w I k (AdicCompletion.evalₐ (polyPointIdeal I w) k x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«GermCompletionEquiv».«evalₐ_toCompl» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_GermCompletionEquiv_eval__toCompl_657f71a1fe27
