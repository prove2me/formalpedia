-- Prove2me | Theorems.Thm_SingleSampleCombPI_XOS_theorem_6_1
-- name    : SingleSampleCombPI.XOS.theorem_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T09:11:23.969921+00:00
-- url     : https://prove2.me/theorems/51697c1a-b72d-4916-afe0-f6fa4b541001
-- title:
--   Theorem 6.1 — efficient 1/(6√3)-competitive single-sample allocation for XOS buyers
-- statement:
--   For indivisible items and XOS buyers, consider Algorithm 3 with the buyer-wise greedy Algorithm 4 as its free-disposal component, Algorithm 7 (symmetric tie-breaking) as its single-item component, and role probability $q=1-1/\sqrt3$. For every number $n$ of buyers and $m$ of items:
--
--   1. it always allocates pairwise disjoint bundles;
--   2. in the single-sample Game of Googol, for every adversarial pair of XOS buyer types per buyer and every real arrival order,
--   $$\mathbb E\Big[\sum_{i=1}^nr_i(S_i)\Big]\ \ge\ \frac{1}{6\sqrt3}\,\mathbb E\Big[\max_{T_1,\dots,T_n\ \text{disjoint}}\sum_{i=1}^nr_i(T_i)\Big],$$
--   the expectation covering the swap coins and all of the algorithm's randomness;
--   3. its running time and its numbers of demand and supporting-price queries are at most $K(n+m+1)^K$ for one constant $K$.
--
--   Here $1/(6\sqrt3)=\tfrac12\cdot\tfrac1{\sqrt3}\cdot\Gamma(1-1/\sqrt3)$ with $\Gamma(q)=q-q^2/2$.
--
--   Differences from the source:
--   - generalization: there is a 1/(6√3)-competitive SSCombPI algorithm with polynomial time and queries → the source's own witness (Algorithm 3 with Algorithms 4 and 7, q = 1 − 1/√3) has these properties; reason: a statement about the witness implies the existential claim; the witness uses the tie-repaired Algorithm 7 of Theorem 5.1
--   - generalization: real buyers arrive in index order → every fixed real arrival order ρ; reason: ρ = identity is the source's statement
--   - reading: runs in polynomial time and uses a polynomial number of demand and supporting-price queries → ∃ K, for all n, m, inputs and random choices: the counts of the defined execution are ≤ K (n + m + 1)^K; reason: the unit-cost oracle model of §3.4, with counts derived from the steps of Algorithms 1–4 and 7
--   - encoding: XOS valuations with oracle access → XOSBuyer: XOS valuation, valid supporting-price oracle, valid demand oracle at nonnegative prices; reason: the source assumes valid oracles (PDF p. 9)
--   - encoding: max over disjoint bundles → Opt .indivisible: sSup of the welfare of feasible 0/1 allocations; reason: a finite nonempty set, so the supremum is the maximum
--   - encoding: a valuation v with its supporting-price map q_v (and, for computation, oracle access) → a record Buyer m with fields v, q (supporting-price oracle) and d (demand oracle) on vectors in ℝ^m, bundles as indicator vectors; reason: values off A^m are never used; the paper's per-valuation map q_v is the record's q
--   - encoding: an algorithm's internal randomness and expected nonnegative reward → an arbitrary probability space of seeds, with nonnegative lower integrals and finite external random choices averaged inside the seed integrals; independent item seeds use iterated expectations; reason: this includes discrete and atomless randomness; on measurable source payoffs these are ordinary expectations under the independent probability laws, without restricting valuation or allocation domains
--   - encoding: expectations and comparisons of nonnegative real quantities → expectations in ℝ≥0∞ of ENNReal.ofReal of the quantities; reason: all compared quantities are nonnegative under the hypotheses, so no instance changes and no integrability convention is needed
-- source:
--   Shuchi Chawla, Trung Dang, STOC 2027 submission #30 (October 2026), SHA-256 d6ed330221fdb64a0d8f70c7d0abbd3346ee1cb8f9e101a745f7e1e57d35230e, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/30.pdf, printed p. 33 / PDF p. 35, Theorem 6.1 and its proof

import Mathlib
import Definitions.Def_SingleSampleCombPI_XOS_Algorithms

namespace SingleSampleCombPI.XOS

/-- **Theorem 6.1** (Chawla–Dang, STOC 2027 submission #30, printed p. 33 / PDF p. 35).  The
single-sample combinatorial online allocation algorithm for indivisible items and XOS buyers —
Algorithm 3 with Algorithm 4 as FDAlg, Algorithm 7 (symmetric tie-breaking) as SSPI and
`q = 1 - 1/√3` — always allocates feasibly, is `1/(6√3)`-competitive in the single-sample Game of
Googol for every number of buyers and items and every real arrival order, and runs in
polynomial time using polynomially many demand and supporting-price queries. -/
theorem theorem_6_1 :
    (∀ (n m : ℕ) (H : Fin n → Bool) (π : Equiv.Perm (Fin n)) (ωs : Fin m → Ranks n)
        (ρ : Equiv.Perm (Fin n)) (s' r' : Fin n → Buyer m),
        (∀ i, XOSBuyer (s' i)) → (∀ i, XOSBuyer (r' i)) →
        Feasible .indivisible (witnessOut n m H π ωs ρ s' r')) ∧
    (∀ (n m : ℕ) (ρ : Equiv.Perm (Fin n)) (V : Fin n → Fin 2 → Buyer m),
        (∀ i t, XOSBuyer (V i t)) →
        ENNReal.ofReal (1 / (6 * Real.sqrt 3)) * optExp1 (A := .indivisible) V ≤
          alg3Exp (alg4 n m) (alg7 n) qStar ρ V) ∧
    ∃ K : ℕ, ∀ (n m : ℕ) (H : Fin n → Bool) (π : Equiv.Perm (Fin n)) (ωs : Fin m → Ranks n)
      (ρ : Equiv.Perm (Fin n)) (s' r' : Fin n → Buyer m),
      Cost.PolyBounded (alg3Cost (alg4 n m) (alg7 n) H π () ωs ρ s' r') K (n + m) := by sorry

end SingleSampleCombPI.XOS
