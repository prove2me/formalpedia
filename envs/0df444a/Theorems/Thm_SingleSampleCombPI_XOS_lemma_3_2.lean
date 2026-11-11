-- Prove2me | Theorems.Thm_SingleSampleCombPI_XOS_lemma_3_2
-- name    : SingleSampleCombPI.XOS.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T09:09:17.974271+00:00
-- url     : https://prove2.me/theorems/7c859440-3854-4f75-b929-9716a1313f11
-- title:
--   Lemma 3.2 — buyer-local composition is αβ-competitive (corrected: supremal divisible benchmark)
-- statement:
--   Let $\mathrm{PAlloc}$ be a buyer-local provisional-allocation algorithm that is $\alpha$-competitive under the free-disposal value, and let a valid $k$-sample single-item algorithm be $\beta$-competitive when real buyers arrive in the order $\rho$. Then Algorithm 1 always outputs a feasible allocation, and in the $(k+1)$-sample Game of Googol, with the $k+2$ valuations of each buyer uniformly permuted into the coordination sample $s^c$, the samples $s^1,\dots,s^k$ and the real valuation $r_i$, and real buyers arriving in order $\rho$,
--   $$\mathbb E\Big[\sum_{i=1}^nr_i(x_i')\Big]\ \ge\ \alpha\beta\,\mathbb E[\mathrm{Opt}(r)].$$
--   The expectation covers the permutations, PAlloc's randomness and the $m$ independent single-item instances. The statement holds for any class of buyer types with supporting prices.
--
--   This is the composition step of the reduction: provisional allocation handles the buyer side, the single-item algorithms the supply side.
--
--   Differences from the source:
--   - correction: Opt(v) = max over feasible allocations (§2.1, PDF p. 8) → Opt A v = sSup of the welfare of feasible allocations; reason: for divisible items the maximum need not exist: n = 2, m = 1, v₁(0) = 0, v₁(x) = 1 for x > 0, v₂(x) = x, with supporting prices q₁(x) = 1/x (x > 0), q₂ = 1, has feasible welfare approaching 2 but never 2; the supremum equals the maximum whenever it is attained, in particular for indivisible items
--   - generalization: valuations with supporting prices → an arbitrary class C of buyer types contained in the valid ones (C b → b.Valid A); reason: the proof uses only properties of the instances in C; C = Valid A is the source's statement
--   - generalization: single-item algorithm competitive with buyers arriving in index order → for an arbitrary fixed real arrival order ρ: if the single-item algorithm is β-competitive under ρ then the combinatorial algorithm is competitive under ρ; reason: ρ = identity is the source's statement
--   - generalization: Algorithm 1 is αβ-competitive → also: Algorithm 1's output is always feasible; reason: the source observes feasibility immediately before the lemma (PDF p. 15); the added clause is an extra conclusion
--   - encoding: a valuation v with its supporting-price map q_v (and, for computation, oracle access) → a record Buyer m with fields v, q (supporting-price oracle) and d (demand oracle) on vectors in ℝ^m, bundles as indicator vectors; reason: values off A^m are never used; the paper's per-valuation map q_v is the record's q
--   - encoding: an algorithm's internal randomness and expected nonnegative reward → an arbitrary probability space of seeds, with nonnegative lower integrals and finite external random choices averaged inside the seed integrals; independent item seeds use iterated expectations; reason: this includes discrete and atomless randomness; on measurable source payoffs these are ordinary expectations under the independent probability laws, without restricting valuation or allocation domains
--   - encoding: expectations and comparisons of nonnegative real quantities → expectations in ℝ≥0∞ of ENNReal.ofReal of the quantities; reason: all compared quantities are nonnegative under the hypotheses, so no instance changes and no integrability convention is needed
-- source:
--   Shuchi Chawla, Trung Dang, STOC 2027 submission #30 (October 2026), SHA-256 d6ed330221fdb64a0d8f70c7d0abbd3346ee1cb8f9e101a745f7e1e57d35230e, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/30.pdf, printed p. 13 / PDF p. 15, Lemma 3.2; proof in Appendix C, PDF pp. 39–40; feasibility from PDF p. 15

import Mathlib
import Definitions.Def_SingleSampleCombPI_XOS_Online

namespace SingleSampleCombPI.XOS

/-- **Lemma 3.2** (Chawla–Dang, STOC 2027 submission #30, printed p. 13 / PDF p. 15; proof in
Appendix C).  If `PAlloc` is buyer-local and `α`-competitive under the free-disposal value and
the `k`-SPI is a valid single-item algorithm that is `β`-competitive under the real arrival
order `ρ`, then Algorithm 1 always outputs a feasible allocation and is `αβ`-competitive in the
`(k+1)`-sample Game of Googol under the arrival order `ρ`.  The buyer class `C` is any class of valuations with supporting prices. -/
theorem lemma_3_2 (A : Regime) {n m k : ℕ} (C : Buyer m → Prop) (hC : ∀ b, C b → b.Valid A)
    (P : PAlloc A n m) (S : KSPI A n k) (α β : ℝ)
    (hP : P.FDCompetitive C α) (hSv : S.Valid) :
    (∀ (ω : P.Ω) (ωs : Fin m → S.Ω) (ρ : Equiv.Perm (Fin n)) (sc : Fin n → Buyer m)
        (s : Fin k → Fin n → Buyer m) (r : Fin n → Buyer m),
        (∀ t i, C (s t i)) → (∀ i, C (r i)) → Feasible A (alg1 P S ω ωs ρ sc s r)) ∧
    ∀ ρ : Equiv.Perm (Fin n), S.Competitive β ρ →
      ∀ V : Fin n → Fin (k + 2) → Buyer m, (∀ i t, C (V i t)) →
      ENNReal.ofReal (α * β) * optExpK (A := A) V ≤ alg1Exp P S ρ V := by sorry

end SingleSampleCombPI.XOS
