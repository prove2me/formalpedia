-- Prove2me | Theorems.Thm_TestScoreSubmod_lemma_2
-- name    : TestScoreSubmod.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:47:20.675987+00:00
-- url     : https://prove2.me/theorems/b9d49b2e-2b7d-4f7b-9e85-4a8d39eff618
-- title:
--   Lemma 2 (corrected: monotone $u$; disjoint sets of size at most $k$ extend to dominated sets)
-- statement:
--   Let $u:2^N\to\mathbb R_+$ be a monotone submodular set function, $0<p$, $0\le q$, $0<k$, and let $\underline v,\bar v:2^N\to\mathbb R$ be a $(p,q)$-sketch of $u$:
--
--   $$
--   p\,\underline v(S)\le u(S)\ \ (|S|=k),\qquad u(S)\le q\,\bar v(S)\ \ (0<|S|\le k).
--   $$
--
--   Let $S^*$ be a set with $|S^*|=k$ such that every nonempty $R\subseteq N\setminus S^*$ with $|R|\le k$ is contained in some $T\subseteq N\setminus S^*$ with $|T|\le k$ and $\bar v(T)\le\underline v(S^*)$. Then for every set $O$ with $|O|=k$, in particular for an optimum set $\mathrm{OPT}$,
--
--   $$
--   u(S^*)\ge\frac{p}{q+p}\,u(O).
--   $$
--
--   A sketch whose majorant on the sets outside $S^*$ is dominated by its minorant on $S^*$ certifies $S^*$ as a $p/(p+q)$-approximation.
--
--   Differences from the source:
--
--   - correction: (b): v̄(S) ≤ v̲(S*) for every S with |S| = k and S ∩ S* = ∅ → every nonempty R ⊆ N ∖ S* with |R| ≤ k lies in some T ⊆ N ∖ S* with |T| ≤ k and v̄(T) ≤ v̲(S*); reason: with n < 2k the printed (b) is vacuous and the lemma fails: N = {1,2,3}, u additive with weights (1,1,10), k = 2, S* = {1,2}, v̲ = 2·1[S = {1,2}], v̄ = u, p = q = 1 gives u(S*) = 2 < 11/2 = ½u({1,3}); the corrected condition follows from the printed one when n ≥ 2k and u is monotone
--   - correction: u a submodular set function → u monotone and submodular; reason: without monotonicity the lemma fails even for n = 2k: u(S) = |S ∩ {1,2}| + 10·1[|S ∩ {3,4}| = 1], k = 2, S* = {1,2}, v̲ = 2·1[S = {1,2}], v̄ = u, p = q = 1 satisfies (b) and gives u(S*) = 2 < 11/2 = ½u({1,3}); p.18 introduces the lemma for monotone submodular functions
--   - generalization: S* ∈ argmax_{|S| = k} v̲(S) → no maximality of S*; reason: the proof never uses it; the Lean statement specializes to the source's
--   - generalization: (8) for all S ⊆ N → lower bound for |S| = k, upper bound for 0 < |S| ≤ k; reason: a weaker hypothesis, implied by (8) on all nonempty sets; these are the only sets the proof uses
--   - reading: a (p, q)-sketch, p and q unspecified → 0 < p, 0 ≤ q; reason: the conclusion's p/(q + p) and the proof's q/p presuppose p > 0, and the proof multiplies v̄(T) ≤ v̲(S*) by q; every sketch of the paper has p, q > 0
--   - encoding: OPT, an optimum set of cardinality k → every O with |O| = k; reason: equivalent: an optimum exists among finitely many sets and u(O) ≤ u(OPT)
--   - encoding: ground set N, u : 2^N → ℝ₊, 0 < k (p.11) → a finite type ι, u : Finset ι → ℝ with 0 ≤ u S, 0 < k as a hypothesis; reason: same instances; k ≤ n follows from the existence of a set of size k
-- source:
--   Sekar, Vojnovic, Yun, A Test Score Based Approach to Stochastic Submodular Optimization, arXiv:1605.07172v4, Lemma 2, p.18; proof in Appendix B, p.34

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular

namespace TestScoreSubmod

/-- **Lemma 2, corrected** (Sekar, Vojnovic, Yun, arXiv:1605.07172v4, Lemma 2, p.18; proof in
Appendix B, p.34).

Let `u : 2^N → ℝ₊` be a monotone submodular set function, `0 < p`, `0 ≤ q`, and let `v̲, v̄` be a
`(p, q)`-sketch of `u`: `p v̲(S) ≤ u(S)` for `|S| = k` and `u(S) ≤ q v̄(S)` for `0 < |S| ≤ k`.
Let `|S*| = k > 0` and suppose that every nonempty `R ⊆ N ∖ S*` with `|R| ≤ k` is contained in
some `T ⊆ N ∖ S*` with `|T| ≤ k` and `v̄(T) ≤ v̲(S*)`. Then `u(S*) ≥ p/(q + p) · u(O)` for every
`O` with `|O| = k`, in particular for an optimum set.

**Formalization Note** The printed lemma is false in two ways: with
`n < 2k` its condition (b) is vacuous (`N = {1,2,3}`, `u` additive with weights `(1,1,10)`,
`k = 2`, `S* = {1,2}`, `v̲ = 2·1[S = {1,2}]`, `v̄ = u`, `p = q = 1`: `u(S*) = 2 < 11/2`), and without
monotonicity of `u` it fails even for `n = 2k` (`u(S) = |S ∩ {1,2}| + 10·1[|S ∩ {3,4}| = 1]`).
The corrected condition replaces "`v̄(S) ≤ v̲(S*)` for every `k`-set `S` disjoint from `S*`"; it
follows from it when `n ≥ 2k` and `u` is monotone. The unused clause `S* ∈ argmax v̲` is
dropped. -/
theorem lemma_2 {ι : Type} [Fintype ι] [DecidableEq ι] (u vl vu : Finset ι → ℝ) (p q : ℝ)
    (k : ℕ) (hk : 0 < k)
    (hu0 : ∀ S, 0 ≤ u S) (humono : Monotone u) (husub : NonmonotoneSubmod.Shared.Submodular u)
    (hp : 0 < p) (hq : 0 ≤ q)
    (hlow : ∀ S : Finset ι, S.card = k → p * vl S ≤ u S)
    (hup : ∀ S : Finset ι, S.Nonempty → S.card ≤ k → u S ≤ q * vu S)
    (Sstar : Finset ι) (hSstar : Sstar.card = k)
    (hb : ∀ R : Finset ι, R.Nonempty → Disjoint R Sstar → R.card ≤ k →
      ∃ T : Finset ι, R ⊆ T ∧ Disjoint T Sstar ∧ T.card ≤ k ∧ vu T ≤ vl Sstar) :
    ∀ O : Finset ι, O.card = k → p / (q + p) * u O ≤ u Sstar := by sorry

end TestScoreSubmod
