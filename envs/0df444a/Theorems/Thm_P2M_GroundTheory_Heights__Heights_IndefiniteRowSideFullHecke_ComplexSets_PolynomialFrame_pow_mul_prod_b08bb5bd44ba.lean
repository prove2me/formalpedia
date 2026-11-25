-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PolynomialFrame_pow_mul_prod_b08bb5bd44ba
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PolynomialFrame_pow_mul_prod_b08bb5bd44ba
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:19:44.749944+00:00
-- url     : https://prove2.me/theorems/20945e09-e292-4450-bdf7-4fc9e066e57f
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Polynomial Frame pow mul prod b08bb5bd44ba: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex S
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Polynomial Frame pow mul prod b08bb5bd44ba construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Polynomial Frame pow mul prod b08bb5bd44ba property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PolynomialFrame.lean#L12-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PolynomialFrame.lean#L12-L25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PolynomialFrame
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
open MvPolynomial Filter Topology
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.PolynomialFrame

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PolynomialFrame_pow_mul_prod_b08bb5bd44ba {k : ℕ} {s : ℂ} (hs : s ≠ 0) (a b : Fin k → ℂ) (m : Fin k →₀ ℕ) {d : ℕ}
    (hm : m.degree ≤ d) :
    s ^ d * ∏ i ∈ m.support, (a i + s⁻¹ * b i) ^ m i =
      s ^ (d - m.degree) * ∏ i ∈ m.support, (s * a i + b i) ^ m i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«PolynomialFrame».«pow_mul_prod» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PolynomialFrame_pow_mul_prod_b08bb5bd44ba
