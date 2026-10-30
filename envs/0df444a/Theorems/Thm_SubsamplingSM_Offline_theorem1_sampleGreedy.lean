-- Prove2me | Theorems.Thm_SubsamplingSM_Offline_theorem1_sampleGreedy
-- name    : SubsamplingSM.Offline.theorem1_sampleGreedy
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:02:15.71713+00:00
-- url     : https://prove2.me/theorems/7c5caaba-5841-46a8-a8f7-aaf789d30948
-- title:
--   Theorem 1 — SampleGreedy: ratios $(p+1)^2/p$, $p+1$, $p$ and the expected oracle calls (corrected: $O(nk/p)$ read as $6n\max(k,1)/p$)
-- statement:
--   Let $N$ be a finite ground set of size $n$ with a fixed (arbitrary) order used to break ties, let $p\ge1$ be an integer, let $(N,\mathcal I)$ be a $p$-extendible system with largest independent set of size $k$, and let $f:2^N\to\mathbb R$ be non-negative. SampleGreedy keeps each element independently with probability $q$ and runs the greedy algorithm on the sample $N'$; write $\mathrm{SG}(N')$ for its output and $\mathbb E_q$ for the expectation over $N'$. Then:
--   1. $\mathrm{SG}(N')\in\mathcal I$ for every sample $N'$;
--   2. if $f$ is submodular and $q=\frac1{p+1}$, then for every $O\in\mathcal I$
--   $$f(O)\le\frac{(p+1)^2}{p}\,\mathbb E_q[f(\mathrm{SG})];$$
--   3. if $f$ is monotone and submodular and $q=\frac1{p+1}$, then for every $O\in\mathcal I$
--   $$f(O)\le(p+1)\,\mathbb E_q[f(\mathrm{SG})];$$
--   4. if $f$ is linear and $q=\frac1p$, then for every $O\in\mathcal I$
--   $$f(O)\le p\,\mathbb E_q[f(\mathrm{SG})];$$
--   5. for $q=\frac1{p+1}$ and for $q=\frac1p$, the expected number of oracle calls of SampleGreedy is at most
--   $$\frac{6\,n\,\max(k,1)}{p}.$$
--
--   Clauses 2–4 say that SampleGreedy is, in expectation, a $(p+1)^2/p$-, $(p+1)$- and $p$-approximation algorithm for maximizing $f$ over $\mathcal I$; clause 5 is its oracle complexity.
--
--   **Formalization Note** Oracle calls are counted by running the loop, with $2|N'|+1$ calls per test of the while condition ($0$ when $N'=\emptyset$), the final failing test included. A linear $f$ need not satisfy $f(\emptyset)=0$.
--
--   Differences from the source:
--   - reading: "achieves an α-approximation ratio" for a randomized algorithm → SG(N′) ∈ I for every sample, and f(O) ≤ α · E_q[f(SG)] for every O ∈ I; reason: paper.md Reading 1: an α-approximation is a set S ∈ I with f(S) ≥ f(OPT)/α (p. 6), and the proofs (pp. 14–15, 17) bound the expectation; OPT ∈ I is an instance and maximizes f over I
--   - encoding: the sample N′ contains each element independently with probability q → E_q[X] = Σ_T q^|T| (1−q)^(n−|T|) X(T); reason: paper.md Reading 1: this is the law of the independent sample; same instances
--   - reading: ties broken in favor of the element earlier in an (arbitrary) ordering of N (p. 10) → an arbitrary LinearOrder α; reason: paper.md Reading 2; footnote 2's other rules are a remark, not part of the theorem
--   - encoding: p, the parameter of the p-extendible system → p : ℕ with 1 ≤ p; reason: paper.md Reading 3: (p+1)²/p and q = p⁻¹ are undefined at p = 0; only that case is excluded
--   - reading: "calls to the evaluation and independence oracles" (no cost model fixed) → the count of the run: 2|N′| + 1 calls per test of the while condition (|N′| independence, |N′| + 1 value), 0 if N′ = ∅, the final failing test included; reason: paper.md Reading 4: the accounting of p. 15; it over-counts any leaner implementation
--   - correction: uses in expectation O(nk/p) calls → E_q[#calls] ≤ 6 · n · max(k, 1) / p for q = 1/(p+1) and q = 1/p; reason: false at k = 0: n = 1, I = {∅} (p-extendible for every p), f ≡ 0, p ≥ 1; whenever N′ ≠ ∅ (probability q > 0) at least one call is needed to learn {u} ∉ I, so E[#calls] ≥ q > 0 = C · nk/p in every cost model; max(k, 1) changes nothing for k ≥ 1 (paper.md Correction 2)
--   - generalization: O(·), an unspecified constant → the explicit constant 6; reason: an explicit absolute constant implies the O-bound
--   - generalization: feasibility S ∈ I and the oracle bound "in all cases" (f non-negative submodular, or linear; q = 1/(p+1), or q = 1/p in the linear case) → clauses 1 and 5 for every non-negative f, and clause 5 at both q for every such f; reason: feasibility follows from the while condition S + u ∈ I and the count only from |S| ≤ k, neither uses submodularity; every case of the source is an instance
-- source:
--   Harshaw, Kazemi, Feldman, Karbasi, The Power of Subsampling in Submodular Maximization, arXiv:2104.02772v1, Theorem 1, p. 7 (proofs: §4.1.1, pp. 14–15, and §4.1.2, p. 17)

import Mathlib
import Definitions.Def_SubsamplingSM_Offline_IsSubmodular
import Definitions.Def_SubsamplingSM_Offline_IsMonotoneSetFn
import Definitions.Def_SubsamplingSM_Offline_IsLinearSetFn
import Definitions.Def_SubsamplingSM_Offline_IsPExtendible
import Definitions.Def_SubsamplingSM_Offline_maxIndepSize
import Definitions.Def_SubsamplingSM_Offline_sampleGreedy
import Definitions.Def_SubsamplingSM_Offline_expectSample
import Definitions.Def_SubsamplingSM_Offline_sgQueries

namespace SubsamplingSM.Offline

/-- **Theorem 1 (SampleGreedy).**
Harshaw, Kazemi, Feldman, Karbasi, *The Power of Subsampling in Submodular Maximization*,
arXiv:2104.02772v1, Theorem 1, p. 7: "When `q = (p + 1)^−1`, SampleGreedy achieves a `(p+1)^2/p`-approximation
ratio for the problem of maximizing a non-negative submodular function f subject to a
p-extendible system. Moreover, this approximation ratio improves to `p + 1` when f is monotone.
When f is linear and `q = p^−1`, SampleGreedy achieves a further improved p-approximation ratio.
In all cases, SampleGreedy uses in expectation `O(nk/p)` calls to the evaluation and
independence oracles."

Let the finite ground set `α` carry any linear order (the tie-breaking order), `p ≥ 1`, `I` a
p-extendible system and `f` non-negative. Write `E_q` for the expectation over the sample
`N′` drawn independently with probability `q`, `SG(N′)` for SampleGreedy's output, `n = |α|`
and `k` for the size of the largest independent set. Then

1. `SG(N′) ∈ I` for every sample;
2. if `f` is submodular, `f(O) ≤ ((p+1)²/p) · E_{1/(p+1)}[f(SG)]` for every `O ∈ I`;
3. if `f` is submodular and monotone, `f(O) ≤ (p+1) · E_{1/(p+1)}[f(SG)]` for every `O ∈ I`;
4. if `f` is linear, `f(O) ≤ p · E_{1/p}[f(SG)]` for every `O ∈ I`;
5. for `q = 1/(p+1)` and `q = 1/p`, the expected number of oracle calls is at most
   `6 · n · max(k, 1) / p`.

**Formalization Note.**
* Reading 1: an `α`-approximation in expectation, `E[f(S)] ≥ f(OPT)/α` with `S ∈ I` always,
  stated against every `O ∈ I` (equivalent to OPT, a maximizer over the finite nonempty `I`);
  the expectation is the exact Bernoulli product sum `expectSample`.
* Reading 2: the tie order is the arbitrary `LinearOrder α` (p. 10).
* Reading 3: `1 ≤ p`, where every ratio and `q` is defined.
* Reading 4: oracle calls are counted by the run `sgQueries` (`2|N′| + 1` per while-test,
  `0` if `N′ = ∅`, final failing test included).
* Correction 2: "`O(nk/p)`" is false at `k = 0` (`n = 1`, `I = {∅}`: at least one call
  whenever `N′ ≠ ∅`); `k` is replaced by `max(k, 1)`, and the explicit constant `6` implies
  the `O(·)` bound.
* A linear `f` need not satisfy `f(∅) = 0`. -/
theorem theorem1_sampleGreedy {α : Type*} [Fintype α] [LinearOrder α]
    (p : ℕ) (hp : 1 ≤ p) (I : Finset α → Prop) (hI : IsPExtendible I p)
    (f : Finset α → ℝ) (hf : ∀ S, 0 ≤ f S) :
    (∀ T : Finset α, I (sampleGreedy f I T)) ∧
    (IsSubmodular f → ∀ O : Finset α, I O →
      f O ≤ (((p : ℝ) + 1) ^ 2 / (p : ℝ)) *
        expectSample (1 / ((p : ℝ) + 1)) (fun T => f (sampleGreedy f I T))) ∧
    (IsSubmodular f → IsMonotoneSetFn f → ∀ O : Finset α, I O →
      f O ≤ ((p : ℝ) + 1) *
        expectSample (1 / ((p : ℝ) + 1)) (fun T => f (sampleGreedy f I T))) ∧
    (IsLinearSetFn f → ∀ O : Finset α, I O →
      f O ≤ (p : ℝ) * expectSample (1 / (p : ℝ)) (fun T => f (sampleGreedy f I T))) ∧
    (∀ q ∈ ({1 / ((p : ℝ) + 1), 1 / (p : ℝ)} : Set ℝ),
      expectSample q (fun T => (sgQueries f I T : ℝ)) ≤
        6 * (Fintype.card α : ℝ) * ((max (maxIndepSize I) 1 : ℕ) : ℝ) / (p : ℝ)) := by sorry

end SubsamplingSM.Offline
