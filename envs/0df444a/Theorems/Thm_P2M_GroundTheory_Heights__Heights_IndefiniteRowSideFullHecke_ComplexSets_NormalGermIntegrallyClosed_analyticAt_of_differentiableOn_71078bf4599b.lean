-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_NormalGermIntegrallyClosed_analyticAt_of_differentiableOn_71078bf4599b
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_NormalGermIntegrallyClosed_analyticAt_of_differentiableOn_71078bf4599b
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:20:33.397501+00:00
-- url     : https://prove2.me/theorems/84615286-d886-4ce6-bae4-41a9b90d954b
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Normal Germ Integrally Closed analytic At of differentiable On 71078bf4599b: P2 M Ground Theory Heights  Heights Indefin
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Normal Germ Integrally Closed analytic At of differentiable On 71078bf4599b construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Normal Germ Integrally Closed analytic At of differentiable On 71078bf4599b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PNormalGermIntegrallyClosed.lean#L16-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PNormalGermIntegrallyClosed.lean#L16-L31

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalGermIntegrallyClosed
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StZariskiAnalyticNormality
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRueckertNullstellensatz
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_OsgoodSeparate
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalGermIntegrallyClosed
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
open MvPolynomial Topology Filter
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.NormalGermIntegrallyClosed

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_NormalGermIntegrallyClosed_analyticAt_of_differentiableOn_71078bf4599b {σ : Type} [Fintype σ] {N : Set (σ → ℂ)} {f : (σ → ℂ) → ℂ}
    (hN : IsOpen N) (hf : DifferentiableOn ℂ f N) {z : σ → ℂ} (hz : z ∈ N) : AnalyticAt ℂ f z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«NormalGermIntegrallyClosed».«analyticAt_of_differentiableOn» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_NormalGermIntegrallyClosed_analyticAt_of_differentiableOn_71078bf4599b
