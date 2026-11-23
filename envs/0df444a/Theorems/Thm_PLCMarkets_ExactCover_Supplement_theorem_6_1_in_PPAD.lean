-- Prove2me | Theorems.Thm_PLCMarkets_ExactCover_Supplement_theorem_6_1_in_PPAD
-- name    : PLCMarkets.ExactCover.Supplement.theorem_6_1_in_PPAD
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T10:21:19.75943+00:00
-- url     : https://prove2.me/theorems/e303d2d6-4a8f-48a8-bf18-d6a323b71e31
-- title:
--   THEOREM 6.1 — exact equilibrium computation is in PPAD for exchange markets under (C') and Fisher markets under (C2)
-- statement:
--   Consider markets with additively separable, piecewise-linear concave utilities and rational data, given by their binary codes.
--
--   1. Let $\mathcal E_k$ be the search problem whose instances are Arrow–Debreu markets (nonempty agents and goods, positive total supplies) satisfying condition (C'), and whose answers are codes of rational price equilibria of length at most $|s|^k+k$ for the input code $s$.
--   2. Let $\mathcal F_k$ be the corresponding search problem for Fisher markets satisfying condition (C2).
--
--   There is $k_0$ such that $\mathcal E_k$ is in PPAD for every $k\ge k_0$, and there is $k_0$ such that $\mathcal F_k$ is in PPAD for every $k\ge k_0$:
--   $$\exists k_0\ \forall k\ge k_0:\ \mathcal E_k\in\mathsf{PPAD},\qquad \exists k_0\ \forall k\ge k_0:\ \mathcal F_k\in\mathsf{PPAD}.$$
--   Membership in PPAD means: the problem is a total search problem (valid instances decidable in polynomial time, answers polynomially bounded and checkable in polynomial time, every valid instance has an answer) with a polynomial-time search reduction to End-of-Line.
--
--   In particular, under these sufficient conditions equilibria exist and have rational prices of polynomial size, and an exact equilibrium can be found by a PPAD computation.
--
--   **Formalization Note** PPAD is the published `CorrelatedAuctionComplexity.Main.InPPAD` (Boolean-circuit End-of-Line, Cook Turing-machine reductions whose answer map is correct for every End-of-Line answer). The problems are those of the `Problems` item.
--
--   Differences from the source:
--   - encoding: the problem of computing an (exact) price equilibrium → total search relations over binary codes whose answers are codes of rational equilibrium price vectors of length at most |s|^k + k, in PPAD for every k from some k₀ on; reason: a PPAD problem must be polynomially balanced; the bound for all large k avoids choosing a particular polynomial
--   - reading: each good totals 1 unit, without loss of generality (§6, p. 10:10) → instances are markets whose goods all have positive total supply; reason: the normalization applies to every such market; the source's input class is the markets given, before normalization
--   - reading: (C') strong connectivity of the economy graph → a path of positive length between every ordered pair of agents; reason: agrees with strong connectivity for two or more agents; for a single agent it requires a loop (the agent owns a good for which it is nonsatiated), which is the reading under which the page's own remarks hold, namely (C') implies (C2), and for Fisher markets (C2) and (C') are equivalent (p. 10:10); with zero-length paths a one-agent satiated economy would satisfy (C') but not (C2)
-- source:
--   Vazirani and Yannakakis, Market Equilibrium under Separable, Piecewise-Linear, Concave Utilities, J. ACM 58(3), Article 10, 2011, p. 10:11, THEOREM 6.1 (conditions (C2), (C') and the equilibrium notion: p. 10:10)

import Mathlib
import Definitions.Def_PLCMarkets_ExactCover_Supplement_Problems

namespace PLCMarkets.ExactCover.Supplement

open CorrelatedAuctionComplexity.Main (InPPAD)

theorem theorem_6_1_in_PPAD :
    (∃ k₀ : ℕ, ∀ k, k₀ ≤ k → InPPAD (exchangeEquilibriumSearch k)) ∧
      ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → InPPAD (fisherEquilibriumSearch k) := by sorry

end PLCMarkets.ExactCover.Supplement
