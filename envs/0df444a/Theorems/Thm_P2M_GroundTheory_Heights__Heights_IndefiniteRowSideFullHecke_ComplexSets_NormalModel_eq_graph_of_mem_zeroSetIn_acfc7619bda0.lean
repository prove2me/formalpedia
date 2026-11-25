-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_NormalModel_eq_graph_of_mem_zeroSetIn_acfc7619bda0
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_NormalModel_eq_graph_of_mem_zeroSetIn_acfc7619bda0
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:20:08.43282+00:00
-- url     : https://prove2.me/theorems/7a156012-f963-4af5-9cba-9a237a6d6546
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Normal Model eq graph of mem zero Set In acfc7619bda0: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Heck
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Normal Model eq graph of mem zero Set In acfc7619bda0 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Normal Model eq graph of mem zero Set In acfc7619bda0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/NormalModelGraph.lean#L90-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/NormalModelGraph.lean#L90-L104

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_NormalModel_eq_graph_of_mem_zeroSetIn_acfc7619bda0 {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    (M : NormalModel J) (a b : Fin M.m → MvPolynomial (Fin n) ℂ)
    (hab : ∀ i, rename Sum.inl (b i) * X (Sum.inr i) - rename Sum.inl (a i) ∈ M.ideal)
    (w : Fin n ⊕ Fin M.m → ℂ) (hw : w ∈ zeroSetIn M.ideal) (hb : ∀ i, eval (firstCoords w) (b i) ≠ 0) :
    w = Sum.elim (firstCoords w) fun i => eval (firstCoords w) (a i) / eval (firstCoords w) (b i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«NormalModel».«eq_graph_of_mem_zeroSetIn» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_NormalModel_eq_graph_of_mem_zeroSetIn_acfc7619bda0
