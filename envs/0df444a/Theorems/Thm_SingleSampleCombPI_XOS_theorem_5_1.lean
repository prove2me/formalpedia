-- Prove2me | Theorems.Thm_SingleSampleCombPI_XOS_theorem_5_1
-- name    : SingleSampleCombPI.XOS.theorem_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T09:11:21.330595+00:00
-- url     : https://prove2.me/theorems/6da8587a-ddcb-480a-ad0c-f05c09dda57f
-- title:
--   Theorem 5.1 — single-sample single-item rule is 1/2-competitive, efficient and optimal (corrected: symmetric tie-breaking)
-- statement:
--   For one indivisible item, Algorithm 7 with symmetric tie-breaking (keys (value, random rank) over all $2n$ sample and real slots; threshold the largest present sampled key, or a sentinel below all keys; accept the first present real buyer whose key exceeds the threshold) satisfies:
--
--   1. it always allocates feasibly;
--   2. it is $\tfrac12$-competitive in the single-sample Game of Googol for every number $n$ of buyers and every real arrival order: $\mathbb E[\sum_iq(r_i)y_i]\ge\tfrac12\,\mathbb E[\mathrm{Opt}(r)]$;
--   3. it runs in polynomial time: at most $K(n+1)^K$ operations for one constant $K$;
--   4. no algorithm does better: for every $\beta>\tfrac12$ and every family of valid single-sample algorithms, one per number of buyers, some number of buyers admits an instance (already with buyers arriving in index order) on which it is not $\beta$-competitive.
--
--   It is the single-item component of the goal.
--
--   Differences from the source:
--   - correction: Algorithm 7: τ = max value of present samples (empty maximum 0); accept the first present real buyer with q(r_i) > τ → keys (q, rank) with uniformly random distinct ranks of the 2n slots, independent of the Game-of-Googol coins; threshold the largest present sampled key, or ⊥ if none; accept the first present real key above it; reason: the printed rule is not 1/2-competitive: one buyer whose two valuations both have value 1 gives τ = 1 and real value 1, so it never accepts (reward 0, prophet 1); replacing > by ≥ also fails (pairs (1,1) and (0,M) in that order give expected reward 1/2 against expected prophet (M+1)/2); the repair keeps every instance and the reward values
--   - generalization: 1/2-competitive with buyers arriving in index order → for every fixed real arrival order ρ; reason: ρ = identity is the source's statement
--   - reading: this is the best competitive ratio achievable by any algorithm → for every β > 1/2 no family of valid single-sample algorithms (one per number of buyers) is β-competitive for all numbers of buyers in index order; reason: a single fixed number of buyers does not suffice (n = 1 allows ratio 1); the source's optimality is uniform in the instance size
--   - reading: polynomial-time → operation counts of the defined decisions and rank draw ≤ K (n + 1)^K; reason: the unit-cost model of §3.4
--   - encoding: an algorithm's internal randomness and expected nonnegative reward → an arbitrary probability space of seeds, with nonnegative lower integrals and finite external random choices averaged inside the seed integrals; independent item seeds use iterated expectations; reason: this includes discrete and atomless randomness; on measurable source payoffs these are ordinary expectations under the independent probability laws, without restricting valuation or allocation domains
--   - encoding: expectations and comparisons of nonnegative real quantities → expectations in ℝ≥0∞ of ENNReal.ofReal of the quantities; reason: all compared quantities are nonnegative under the hypotheses, so no instance changes and no integrability convention is needed
-- source:
--   Shuchi Chawla, Trung Dang, STOC 2027 submission #30 (October 2026), SHA-256 d6ed330221fdb64a0d8f70c7d0abbd3346ee1cb8f9e101a745f7e1e57d35230e, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/30.pdf, printed p. 27 / PDF p. 29, Theorem 5.1 and Algorithm 7 (after Rubinstein–Wang–Weinberg 2020)

import Mathlib
import Definitions.Def_SingleSampleCombPI_XOS_Algorithms

namespace SingleSampleCombPI.XOS

/-- **Theorem 5.1** (Chawla–Dang, STOC 2027 submission #30, printed p. 27 / PDF p. 29; after
[RWW20]), for Algorithm 7 with symmetric random tie-breaking.  Algorithm 7 is a valid
single-sample single-item algorithm for the indivisible item, `1/2`-competitive in the Game of
Googol for every number of buyers and every real arrival order, and runs in polynomial time;
and no algorithm (family over all numbers of buyers) achieves any competitive ratio
`β > 1/2`, already when the real buyers arrive in index order. -/
theorem theorem_5_1 :
    (∀ n : ℕ, (alg7 n).Valid) ∧
    (∀ (n : ℕ) (ρ : Equiv.Perm (Fin n)), (alg7 n).Competitive (1 / 2) ρ) ∧
    (∃ K : ℕ, ∀ (n : ℕ) (ω : (alg7 n).Ω) (s : Fin 1 → Fin n → Item) (ρ : Equiv.Perm (Fin n))
      (r : Fin n → Item), spiCost (alg7 n) ω s ρ r ≤ K * (n + 1) ^ K) ∧
    ∀ β : ℝ, 1 / 2 < β → ∀ S : (n : ℕ) → KSPI .indivisible n 1,
      (∀ n, (S n).Valid) → ¬ ∀ n, (S n).Competitive β (Equiv.refl (Fin n)) := by sorry

end SingleSampleCombPI.XOS
