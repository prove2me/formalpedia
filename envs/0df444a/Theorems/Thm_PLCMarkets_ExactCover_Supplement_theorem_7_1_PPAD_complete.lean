-- Prove2me | Theorems.Thm_PLCMarkets_ExactCover_Supplement_theorem_7_1_PPAD_complete
-- name    : PLCMarkets.ExactCover.Supplement.theorem_7_1_PPAD_complete
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T10:22:21.482872+00:00
-- url     : https://prove2.me/theorems/735dc8f5-8080-444a-98c8-e859832ef137
-- title:
--   THEOREM 7.1 — exact and $\nu_7(g)^{-13}$-approximate Fisher equilibrium computation under (C2) are PPAD-complete
-- statement:
--   Consider Fisher markets with additively separable piecewise-linear concave utilities and rational data that satisfy condition (C2), given by their binary codes. For a market with $g$ goods let $\nu_7(g)=\max(1,\lceil(g-2)/2\rceil)$, so $\nu_7(2n+2)=n$.
--
--   1. Let $\mathcal F_k$ be the search problem whose answers are codes of rational price equilibria of length at most $|s|^k+k$.
--   2. Let $\mathcal A_k$ be the search problem whose answers are codes of rational $\varepsilon$-approximate equilibria of length at most $|s|^k+k$, where
--   $$\varepsilon=\nu_7(g)^{-13}.$$
--
--   There is $k_0$ such that $\mathcal F_k$ is PPAD-complete for every $k\ge k_0$, and there is $k_0$ such that $\mathcal A_k$ is PPAD-complete for every $k\ge k_0$. PPAD-complete means in PPAD and PPAD-hard: every problem in PPAD has a polynomial-time search reduction to it.
--
--   Together with Theorem 6.1 this places exact Fisher equilibrium computation under (C2) exactly at the level of PPAD, and shows that the hardness persists for polynomially small approximation.
--
--   **Formalization Note** PPAD-completeness is the published `CorrelatedAuctionComplexity.Main.PPADComplete`. The approximate equilibrium is the unit-supply form of the §7 notion (`SourceEquilibrium` item): prices sum to the total budget and every good clears within $\varepsilon$.
--
--   Differences from the source:
--   - reading: ε = O(n^-13), n the number of strategies of each player (§7, p. 10:16) → ε = ν₇(g)^-13 with ν₇(g) = max(1, ⌈(g − 2)/2⌉) for a market with g goods; reason: the proof fixes ε = n^-13 with coefficient 1 (p. 10:17); its Fisher instance has g = 2n + 2 goods, where ν₇(g) = n, and ν₇ is defined on every market
--   - encoding: computing a price equilibrium (exact or ε-approximate) → total search relations whose answers are codes of rational (approximate) equilibrium price vectors of length at most |s|^k + k, PPAD-complete for every k from some k₀ on; reason: a PPAD problem must be polynomially balanced
--   - encoding: ε-approximate equilibrium of a Fisher market with M units of each good: Σ p_j = 1, |Σ_i x_ij − M| ≤ εM (p. 10:17) → unit supply: Σ p_j = Σ_i e(i), |Σ_i x_ij − 1| ≤ ε; reason: measuring goods in units of M (the §2 normalization) maps the one notion onto the other
-- source:
--   Vazirani and Yannakakis, Market Equilibrium under Separable, Piecewise-Linear, Concave Utilities, J. ACM 58(3), Article 10, 2011, p. 10:16, THEOREM 7.1 (ε-approximate equilibria: pp. 10:16–10:17; ε = n^-13: p. 10:17)

import Mathlib
import Definitions.Def_PLCMarkets_ExactCover_Supplement_Problems

namespace PLCMarkets.ExactCover.Supplement

open CorrelatedAuctionComplexity.Main (PPADComplete)

theorem theorem_7_1_PPAD_complete :
    (∃ k₀ : ℕ, ∀ k, k₀ ≤ k → PPADComplete (fisherEquilibriumSearch k)) ∧
      ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → PPADComplete (fisherApproxEquilibriumSearch k) := by sorry

end PLCMarkets.ExactCover.Supplement
