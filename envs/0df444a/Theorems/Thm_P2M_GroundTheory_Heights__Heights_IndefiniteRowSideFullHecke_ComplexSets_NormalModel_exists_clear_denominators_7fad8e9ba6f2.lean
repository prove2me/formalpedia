-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_NormalModel_exists_clear_denominators_7fad8e9ba6f2
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_NormalModel_exists_clear_denominators_7fad8e9ba6f2
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:19:55.159474+00:00
-- url     : https://prove2.me/theorems/6df20daa-a789-4d0d-9c6c-30e0d5a3efaa
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Normal Model exists clear denominators 7fad8e9ba6f2: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Normal Model exists clear denominators 7fad8e9ba6f2 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Normal Model exists clear denominators 7fad8e9ba6f2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/NormalModelGraph.lean#L9-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/NormalModelGraph.lean#L9-L67

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_NormalModel_exists_clear_denominators_7fad8e9ba6f2 {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    (M : NormalModel J) (a b : Fin M.m → MvPolynomial (Fin n) ℂ)
    (hab : ∀ i, rename Sum.inl (b i) * X (Sum.inr i) - rename Sum.inl (a i) ∈ M.ideal)
    (x : Fin n → ℂ) (hb : ∀ i, eval x (b i) ≠ 0) (q : MvPolynomial (Fin n ⊕ Fin M.m) ℂ) :
    ∃ (N : ℕ) (r : MvPolynomial (Fin n) ℂ),
      rename Sum.inl ((∏ i, b i) ^ N) * q - rename Sum.inl r ∈ M.ideal ∧
        eval x r = eval x (∏ i, b i) ^ N *
          eval (Sum.elim x fun i => eval x (a i) / eval x (b i)) q := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«NormalModel».«exists_clear_denominators» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_NormalModel_exists_clear_denominators_7fad8e9ba6f2
