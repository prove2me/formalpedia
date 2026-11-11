-- Prove2me | Theorems.Thm_PriceCapacities_LowerBound_lemma_10_5
-- name    : PriceCapacities.LowerBound.lemma_10_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:24:28.118233+00:00
-- url     : https://prove2.me/theorems/30cf2088-d8ad-43a7-80ad-7f2667a07009
-- title:
--   Lemma 10.5 — priced comparison: $|f_{C,\beta}(Q)-f_{C,\beta}(P)|\le\varepsilon L$
-- statement:
--   Let $z\ge1$ be an integer, $0<\varepsilon<1/4$, and $P$ a finite weighted point set in $\mathbb R^d$ with a capacitated $\varepsilon$-coreset $Q$ for $k$ centers. Fix a center tuple $C=(c_1,\dots,c_k)$ and prices $\beta\in\mathbb R^k$, and for each $p\in P$ choose a center $c_{i(p)}$ minimizing $(1-\varepsilon)\|p-c_i\|^z+\beta_i$ (ties arbitrary). Let
--   $$L=\sum_{p\in P}P(p)\,\|p-c_{i(p)}\|^z$$
--   be the clustering cost of this assignment before adding the prices. Then, with $f_{C,\beta}(y)=\min_i\{\|y-c_i\|^z+\beta_i\}$,
--   $$\big|f_{C,\beta}(Q)-f_{C,\beta}(P)\big|\le\varepsilon L .$$
--   This converts the coreset guarantee for prescribed loads into a guarantee for every priced nearest-center cost, which is how the queries of Lemmas 10.2 and 10.3 are evaluated.
--
--   Differences from the source:
--
--   - generalization: P the hard instance of §10.3 (k ≥ 4) and Q a capacitated ε-coreset for it → P any finite weighted point set in any ℝ^d, any k, Q any capacitated ε-coreset for P; reason: the lemma and its proof use only Definition 2.2 for P and Q; the instance is a special case
--   - encoding: for each p ∈ P choose a minimizing center → σ : ℝ^d → Fin k with (1 − ε)‖p − c_{σ p}‖^z + β_{σ p} ≤ (1 − ε)‖p − c_i‖^z + β_i for every p ∈ supp P and every i; reason: any minimizer, ties arbitrary; values of σ off supp P do not enter
--   - reading: ε, z from the standing assumptions of §10 → 0 < ε < 1/4 (Theorem 10.1), z : ℕ with 1 ≤ z; reason: §10 fixes an integer z ≥ 1 and works in the range of Theorem 10.1
-- source:
--   Prabhu, Schwiegelshohn, Shyam, The Price of Capacities for Clustering Coresets, STOC 2027 submission (manuscript sha256 ec35f5ef…), p. 35, Lemma 10.5

import Mathlib
import Definitions.Def_PriceCapacities_LowerBound_WeightedSets
import Definitions.Def_PriceCapacities_LowerBound_CapacitatedCost
import Definitions.Def_PriceCapacities_LowerBound_CapacitatedCoreset
import Definitions.Def_PriceCapacities_LowerBound_DualCost

namespace PriceCapacities.LowerBound

theorem lemma_10_5 (d k z : ℕ) (hz : 1 ≤ z) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 4)
    (P Q : WeightedSet (EuclideanSpace ℝ (Fin d)))
    (hQ : IsCapacitatedCoreset k (z : ℝ) ε P Q)
    (C : Fin k → EuclideanSpace ℝ (Fin d)) (β : Fin k → ℝ)
    (σ : EuclideanSpace ℝ (Fin d) → Fin k)
    (hσ : ∀ p ∈ P.support, ∀ i : Fin k,
      (1 - ε) * dist p (C (σ p)) ^ (z : ℝ) + β (σ p) ≤ (1 - ε) * dist p (C i) ^ (z : ℝ) + β i) :
    |wsum Q (pricedCost (z : ℝ) C β) - wsum P (pricedCost (z : ℝ) C β)|
      ≤ ε * wsum P (fun p => dist p (C (σ p)) ^ (z : ℝ)) := by sorry

end PriceCapacities.LowerBound
