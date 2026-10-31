-- Prove2me | Theorems.Thm_TestScoreSubmod_corollary_1
-- name    : TestScoreSubmod.corollary_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:48:11.350614+00:00
-- url     : https://prove2.me/theorems/adb5bc82-c35f-4724-a252-5c05cd17552d
-- title:
--   Corollary 1: selecting the top $k$ by $(p,q)$-good scores is a $p/(p+q)$-approximation
-- statement:
--   Let $u:2^N\to\mathbb R_+$ be a monotone submodular set function, $0<k$, $0<p$, $0\le q$, and let the test scores $a_1,\dots,a_n$ be $(p,q)$-good for $u$:
--
--   $$
--   p\min_{i\in S}a_i\le u(S)\ \ (|S|=k),\qquad u(S)\le q\max_{i\in S}a_i\ \ (S\neq\emptyset,\ |S|\le k).
--   $$
--
--   Then every set $S$ of $k$ items with the largest scores (greedy selection in decreasing order of the scores, under any tie-breaking) satisfies
--
--   $$
--   u(S)\ge\frac{p}{p+q}\,u(T)\qquad\text{for every }T\text{ with }|T|=k,
--   $$
--
--   in particular for an optimum set. If $p/q$ is a constant, greedy selection by these scores is a constant-factor approximation for maximizing $u$ under the constraint $|S|=k$.
--
--   Differences from the source:
--
--   - generalization: (p, q)-good: (v̲, v̄) = (min a, max a) a (p, q)-sketch (8) for all S ⊆ N → IsGoodScores: lower bound for |S| = k, upper bound for 0 < |S| ≤ k; reason: a weaker hypothesis, implied by (8) on all nonempty sets (min and max of ∅ are undefined); it is what Lemma 4 delivers
--   - reading: the set function u (§3: a stochastic monotone submodular function) → u ≥ 0, monotone and submodular; reason: §2.2 and §3 study maximizing a stochastic monotone submodular function (Lemma 1), and p.18 introduces the sketch results for monotone functions; without monotonicity the corollary fails: N = {1,2,3}, a = (10,1,0), k = 2, p = q = 1, u(∅) = 0, u({1}) = 10, u({2}) = 1, u({3}) = 0, u({1,2}) = 1, u({1,3}) = 10, u({2,3}) = 1, u(N) = 1 is nonnegative and submodular with (8) on all nonempty S, and the top-2 set gives u({1,2}) = 1 < 5 = ½u({1,3})
--   - reading: (p, q), unspecified → 0 < p, 0 ≤ q; reason: p/(p + q) presupposes it; every pair in the paper has p, q > 0
--   - reading: greedy selection of items in decreasing order of these test scores; the optimum value → every S with IsTopK a k S; every T with |T| = k; reason: covers every tie-breaking rule and, since an optimum exists among finitely many sets, the optimum
--   - encoding: ground set N, u : 2^N → ℝ₊, 0 < k (p.11) → a finite type ι, u : Finset ι → ℝ with 0 ≤ u S, 0 < k as a hypothesis; reason: same instances; k ≤ n follows from the existence of a set of size k
-- source:
--   Sekar, Vojnovic, Yun, A Test Score Based Approach to Stochastic Submodular Optimization, arXiv:1605.07172v4, Corollary 1, p.19

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_TestScoreSubmod_IsTopK
import Definitions.Def_TestScoreSubmod_IsGoodScores

namespace TestScoreSubmod

/-- **Corollary 1, corrected** (Sekar, Vojnovic, Yun, arXiv:1605.07172v4, Corollary 1, p.19).

Let `u : 2^N → ℝ₊` be a monotone submodular set function, `0 < p`, `0 ≤ q`, `0 < k`, and let
the test scores `a₁, …, aₙ` be `(p, q)`-good for `u` (`IsGoodScores`). Then every set `S` of `k`
items with the largest test scores (any tie-breaking) satisfies `u(S) ≥ p/(p + q) · u(T)` for
every `T` with `|T| = k`, in particular for an optimum set.

**Formalization Note** The `(p, q)`-good condition is required with the lower bound at `|S| = k`
and the upper bound at `0 < |S| ≤ k` (see `IsGoodScores`); when `n < 2k` the upper bound at
`|S| = k` alone does not give the corollary. Monotonicity of `u` is added, as for Lemma 2, of
which this is the case `v̲ = min a`, `v̄ = max a`; in the paper `u` is a stochastic monotone
submodular function (Lemma 1). -/
theorem corollary_1 {ι : Type} [Fintype ι] [DecidableEq ι] (u : Finset ι → ℝ) (a : ι → ℝ)
    (p q : ℝ) (k : ℕ) (hk : 0 < k)
    (hu0 : ∀ S, 0 ≤ u S) (humono : Monotone u) (husub : NonmonotoneSubmod.Shared.Submodular u)
    (hp : 0 < p) (hq : 0 ≤ q) (hgood : IsGoodScores k p q a u)
    (S : Finset ι) (hS : IsTopK a k S) :
    ∀ T : Finset ι, T.card = k → p / (p + q) * u T ≤ u S := by sorry

end TestScoreSubmod
