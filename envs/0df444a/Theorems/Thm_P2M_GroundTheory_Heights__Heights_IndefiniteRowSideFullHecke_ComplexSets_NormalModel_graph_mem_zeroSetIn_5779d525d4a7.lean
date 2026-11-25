-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_NormalModel_graph_mem_zeroSetIn_5779d525d4a7
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_NormalModel_graph_mem_zeroSetIn_5779d525d4a7
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:20:08.054858+00:00
-- url     : https://prove2.me/theorems/926f0236-d8c5-41cb-8aa1-96076b6d0195
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Normal Model graph mem zero Set In 5779d525d4a7: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Comp
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Normal Model graph mem zero Set In 5779d525d4a7 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Normal Model graph mem zero Set In 5779d525d4a7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/NormalModelGraph.lean#L69-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/NormalModelGraph.lean#L69-L88

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_NormalModelGraph
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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_NormalModel_graph_mem_zeroSetIn_5779d525d4a7 {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    (M : NormalModel J) (a b : Fin M.m → MvPolynomial (Fin n) ℂ)
    (hab : ∀ i, rename Sum.inl (b i) * X (Sum.inr i) - rename Sum.inl (a i) ∈ M.ideal)
    (x : Fin n → ℂ) (hx : x ∈ zeroSetIn J) (hb : ∀ i, eval x (b i) ≠ 0) :
    (Sum.elim x fun i => eval x (a i) / eval x (b i)) ∈ zeroSetIn M.ideal := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«NormalModel».«graph_mem_zeroSetIn» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_NormalModel_graph_mem_zeroSetIn_5779d525d4a7
