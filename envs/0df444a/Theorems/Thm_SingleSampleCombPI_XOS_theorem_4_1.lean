-- Prove2me | Theorems.Thm_SingleSampleCombPI_XOS_theorem_4_1
-- name    : SingleSampleCombPI.XOS.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T09:11:02.944326+00:00
-- url     : https://prove2.me/theorems/c753db39-97d4-4ffe-b7c5-bbcd5c66b62b
-- title:
--   Theorem 4.1 — Algorithm 4 is 0.5096-competitive, (q − q²/2)-smooth and efficient for XOS buyers
-- statement:
--   For XOS buyers (with valid supporting-price and demand oracles) arriving in a uniformly random order, the buyer-wise greedy Algorithm 4 is
--
--   1. $0.5096$-competitive under the free-disposal value: $\mathbb E_\pi[\mathrm{FD}(S_1,\dots,S_n)]\ge0.5096\cdot\mathrm{Opt}(v)$;
--   2. $\Gamma$-smooth-competitive with $\Gamma(q)=q-q^2/2$ (Definition 10);
--   3. efficient: one run on $n$ buyers and $m$ items uses at most $K(n+m+1)^K$ primitive operations, demand queries and supporting-price queries, for one constant $K$.
--
--   It is the free-disposal component of the goal.
--
--   Differences from the source:
--   - reading: runs in polynomial time and uses polynomially many demand and supporting-price queries → ∃ K, for all n, m, inputs: operation, demand-query and supporting-price-query counts of the defined run are ≤ K (n + m + 1)^K; reason: the unit-cost oracle model of §3.4, with counts derived from the steps of Algorithm 4
--   - encoding: buyers with XOS valuations (and oracle access) → XOSBuyer: XOS valuation, valid supporting-price oracle (Definition 1), valid demand oracle at nonnegative prices; reason: the source assumes valid oracles (PDF p. 9); Algorithm 4 queries only nonnegative prices
--   - encoding: 0.5096 → 637/1250; reason: the same exact decimal
--   - encoding: a valuation v with its supporting-price map q_v (and, for computation, oracle access) → a record Buyer m with fields v, q (supporting-price oracle) and d (demand oracle) on vectors in ℝ^m, bundles as indicator vectors; reason: values off A^m are never used; the paper's per-valuation map q_v is the record's q
--   - encoding: expectations and comparisons of nonnegative real quantities → expectations in ℝ≥0∞ of ENNReal.ofReal of the quantities; reason: all compared quantities are nonnegative under the hypotheses, so no instance changes and no integrability convention is needed
-- source:
--   Shuchi Chawla, Trung Dang, STOC 2027 submission #30 (October 2026), SHA-256 d6ed330221fdb64a0d8f70c7d0abbd3346ee1cb8f9e101a745f7e1e57d35230e, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/30.pdf, printed p. 18 / PDF p. 20, Theorem 4.1; proof PDF p. 22

import Mathlib
import Definitions.Def_SingleSampleCombPI_XOS_Algorithms

namespace SingleSampleCombPI.XOS

/-- **Theorem 4.1** (Chawla–Dang, STOC 2027 submission #30, printed p. 18 / PDF p. 20).  For
XOS buyers (with valid supporting-price and demand oracles) arriving in a uniformly random
order, Algorithm 4 is `0.5096`-competitive and `Γ`-smooth-competitive under the free-disposal
value, `Γ(q) = q - q²/2`; and it runs in polynomial time with polynomially many demand and
supporting-price queries. -/
theorem theorem_4_1 :
    (∀ n m : ℕ, (alg4 n m).FDCompetitive XOSBuyer (637 / 1250)) ∧
    (∀ n m : ℕ, (alg4 n m).Smooth XOSBuyer (fun q => q - q ^ 2 / 2)) ∧
    ∃ K : ℕ, ∀ (n m : ℕ) (ω : (alg4 n m).Ω) (π : Equiv.Perm (Fin n)) (v : Fin n → Buyer m),
      Cost.PolyBounded (fdRunCost (alg4 n m) ω π v) K (n + m) := by sorry

end SingleSampleCombPI.XOS
