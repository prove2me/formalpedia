-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_germQuotPointIdeal_le_jacobson_60b0c1ad5c75
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_germQuotPointIdeal_le_jacobson_60b0c1ad5c75
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:21:12.721804+00:00
-- url     : https://prove2.me/theorems/cdeb85c3-d034-4a5d-bfcf-20dc47abc984
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets germ Quot Point Ideal le jacobson 60b0c1ad5c75: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Compl
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets germ Quot Point Ideal le jacobson 60b0c1ad5c75 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets germ Quot Point Ideal le jacobson 60b0c1ad5c75 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PZariskiAnalyticNormality.lean#L32-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PZariskiAnalyticNormality.lean#L32-L40

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHolGermsNoetherian
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCompletionNormalDescent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAffineCompletionNormal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGermCompletionEquiv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PZariskiAnalyticNormality
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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_germQuotPointIdeal_le_jacobson_60b0c1ad5c75 {σ : Type} [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) :
    germQuotPointIdeal I w ≤ (⊥ : Ideal (holGerms w ⧸ I.map (polyGerm w))).jacobson := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«germQuotPointIdeal_le_jacobson» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_germQuotPointIdeal_le_jacobson_60b0c1ad5c75
