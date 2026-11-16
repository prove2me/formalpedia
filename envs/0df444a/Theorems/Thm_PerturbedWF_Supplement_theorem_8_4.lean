-- Prove2me | Theorems.Thm_PerturbedWF_Supplement_theorem_8_4
-- name    : PerturbedWF.Supplement.theorem_8_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:10:49.218815+00:00
-- url     : https://prove2.me/theorems/86e8608f-2f24-44e6-8eb6-753d7f3c669b
-- title:
--   Theorem 8.4: weighted paging reduces to LPPP; both competitive ratios lie in $[L_k,L_k+1+o(1)]$
-- statement:
--   For each $k\ge1$ and $\rho_k\ge1$: if there is a $\rho_k$-competitive (randomized online) algorithm for weighted paging with cache size $k$, then there is a $\rho_k$-competitive algorithm for the laminar parking permit problem (LPPP) with $k$ permit types. Consequently, both problems have a competitive ratio in the interval
--   $$[L_k,\ L_k+1+o(1)],\qquad L_1=1,\quad L_{k+1}=\frac{L_k}{1-e^{-L_k}}.$$
--   Explicitly:
--
--   1. the reduction above;
--   2. every $\rho$ for which a $\rho$-competitive weighted-paging algorithm with cache size $k$ exists satisfies $\rho\ge L_k$;
--   3. every $\rho$ for which a $\rho$-competitive LPPP algorithm with $k$ permit types exists satisfies $\rho\ge L_k$;
--   4. there are $\varepsilon_k\to0$ such that both problems admit $(L_k+1+\varepsilon_k)$-competitive algorithms for every $k\ge1$.
--
--   Since $L_k=\ln k+\ln\ln k+o(1)$, this settles the competitive ratio of weighted paging up to an additive $1+o(1)$ (previously a multiplicative gap) and slightly improves the upper bound for LPPP.
--
--   **Formalization Note** A randomized online algorithm is a probability distribution over deterministic online algorithms (functions of the request prefix), compared against a fixed request sequence; $\rho$-competitive allows an additive constant independent of the request sequence. Weighted paging pays the movement cost and its OPT is the minimum of the work function (8.1); LPPP's OPT is the cheapest covering purchase plan. The interval statement is written through these predicates, without a real infimum.
--
--   Differences from the source:
--   - reading: 'both problems have a competitive ratio in the interval [L_k, L_k + 1 + o(1)]' → (2), (3): every achievable ratio ρ satisfies L_k ≤ ρ; (4): ∃ ε_k → 0 with (L_k + 1 + ε_k)-competitive algorithms for both problems for every k ≥ 1; reason: the competitive ratio is the infimum of the achievable ratios; these clauses say exactly that the infimum lies in the interval, and avoid the junk value of a real sInf
--   - encoding: ρ_k-competitive (randomized) algorithm → IsCompetitiveWP / IsCompetitiveLPPP: for every instance a probability measure on deterministic online algorithms (functions of the request prefix), valid almost surely, and C with E[cost] ≤ ρ·OPT + C for every horizon and request sequence; reason: the standard oblivious-adversary model with an additive constant, which the proof uses ('for some constant C > 0')
--   - encoding: k ∈ ℕ (cache size, number of permit types) → k ≥ 1; reason: L_k is defined from L_1; with k = 0 no paging algorithm can serve a request
--   - encoding: laminar type-i intervals {aD_i + 1, …, (a + 1)D_i}; a permit bought on day s is active until the end of the current type-i interval → IsLaminar (pairwise disjoint or nested intervals) with D_i ≥ 1; active on day t iff s ≤ t and ⌊(t − 1)/D_i⌋ = ⌊(s − 1)/D_i⌋; at most one permit of each type per day; reason: the same rules; a second identical permit on the same day is never useful
-- source:
--   Coester, Kashaev, Online Metric Problems via Randomly Perturbed Work Functions (STOC 2027 submission, held version, sha256 e2e30a44…), Theorem 8.4, p.23 (PDF p.24); the LPPP definition and L_k ([CT26]) of §8.2.3, p.23 (PDF p.24); the weighted paging model of §8.1–§8.2, pp.20–22 (PDF pp.21–23)

import Mathlib
import Definitions.Def_PerturbedWF_Supplement_LPPP

namespace PerturbedWF.Supplement

open Filter Topology

/-- **Theorem 8.4** (p.23, PDF p.24). C. Coester, D. Kashaev, *Online Metric Problems via Randomly
Perturbed Work Functions*, STOC 2027 submission (held version, sha256 e2e30a44…).

For each `k ∈ ℕ` and `ρ_k ≥ 1`, if there is a `ρ_k`-competitive algorithm for weighted paging with
cache size `k`, then there is a `ρ_k`-competitive algorithm for LPPP with `k` permit types.
Consequently, both problems have a competitive ratio in the interval `[L_k, L_k + 1 + o(1)]`,
with `L_1 = 1`, `L_{k+1} = L_k/(1 − e^{−L_k})`.

The statement has four clauses: (1) the reduction; (2), (3) every `ρ` for which a `ρ`-competitive
randomized algorithm exists is at least `L_k`, for weighted paging and for LPPP (the lower end of
the interval: the competitive ratio, the infimum of such `ρ`, is `≥ L_k`); (4) there are
`ε_k → 0` such that both problems admit `(L_k + 1 + ε_k)`-competitive randomized algorithms (the
upper end).

**Formalization Note.** Competitiveness (`IsCompetitiveWP`, `IsCompetitiveLPPP`) is against a
fixed request sequence, for a probability distribution over deterministic online algorithms,
with an additive constant independent of the request sequence; weighted paging pays the movement
cost of §8.1. The competitive ratio is stated through these two predicates rather than as a real
infimum, so no junk value of an empty or unbounded set can enter. `k ≥ 1` (permit types and
cache size; `L_k` starts at `k = 1`). -/
theorem theorem_8_4 :
    (∀ k : ℕ, 1 ≤ k → ∀ ρ : ℝ, 1 ≤ ρ → IsCompetitiveWP k ρ → IsCompetitiveLPPP k ρ) ∧
    (∀ k : ℕ, 1 ≤ k → ∀ ρ : ℝ, IsCompetitiveWP k ρ → Lseq k ≤ ρ) ∧
    (∀ k : ℕ, 1 ≤ k → ∀ ρ : ℝ, IsCompetitiveLPPP k ρ → Lseq k ≤ ρ) ∧
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ k : ℕ, 1 ≤ k →
        IsCompetitiveWP k (Lseq k + 1 + ε k) ∧ IsCompetitiveLPPP k (Lseq k + 1 + ε k) := by sorry

end PerturbedWF.Supplement
