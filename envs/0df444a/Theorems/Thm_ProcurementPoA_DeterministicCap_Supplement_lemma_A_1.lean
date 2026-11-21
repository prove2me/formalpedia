-- Prove2me | Theorems.Thm_ProcurementPoA_DeterministicCap_Supplement_lemma_A_1
-- name    : ProcurementPoA.DeterministicCap.Supplement.lemma_A_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-15T17:38:20.311916+00:00
-- url     : https://prove2.me/theorems/12d27e75-b7f5-4455-8134-326d4f8a3f65
-- title:
--   Lemma A.1 — For every acceptance function S and x ≥ 1, the monopoly profit of cost 1 dominates the integral of σ: π(1) ≥ ∫_1^x σ(t) dt.
-- statement:
--   Let $R\ge1$ and let $S(b)=\Pr[Z\ge b]$ be the acceptance function of any Borel phantom law with $Z\le R$ almost surely. Let $\pi(c)=\sup_b(b-c)S(b)$ and let $\sigma(c)$ be the acceptance probability at its largest maximizing bid, with the zero-profit conventions of Definition 5.4. For every real $x\ge1$,
--   $$\int_1^x\sigma(t)\,dt\le\pi(1).$$
--   This holds for all $x\ge1$, including $x>R$, without regularity, continuity or density hypotheses on the phantom law. It controls acceptance probabilities through the cheapest supplier's monopoly profit.
--
--   **Formalization Note** On $[1,\infty)$ the function $\sigma$ is bounded, nonincreasing, and zero from $R$ onward, so its real interval integral is the genuine finite integral, including when $x>R$.
--
--   Differences from the source:
--   - generalization: the nondegenerate normalized phantom interval → R ≥ 1 including R = 1; reason: then monopoly profit at cost 1 and sigma on [1,∞) are zero, so the endpoint preserves the bound
--   - encoding: an acceptance function and its integral → the survival function of an actual Borel probability law, real largest-maximizer suprema with the zero-profit branch, and a real interval integral; reason: keeps atoms and the source conventions; bounded monotonicity ensures interval integrability rather than a default nonintegrable integral
-- source:
--   Simone Palazzotto, Andrés Cristi, At What Cost? (In)efficiency in First-Price Procurement Auctions, STOC 2027 submission #293 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/293.pdf, Lemma A.1, printed p. 17 (PDF p. 19)

import Mathlib
import Definitions.Def_ProcurementPoA_DeterministicCap_Supplement_Monopoly

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology Classical

namespace ProcurementPoA.DeterministicCap.Supplement

/-- Every x ≥ 1, including x > R; no regularity or density restriction. -/
theorem lemma_A_1 (R : ℝ) (hR : 1 ≤ R) (S : ℝ → ℝ) (hS : IsAcceptance R S)
    (x : ℝ) (hx : 1 ≤ x) :
    (∫ t in (1 : ℝ)..x, sigma R S t) ≤ monopolyProfit S 1 := by sorry

end ProcurementPoA.DeterministicCap.Supplement
