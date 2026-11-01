-- Prove2me | Theorems.Thm_WildeQIT_ZhangAudenaert_zhang_audenaert
-- name    : WildeQIT.ZhangAudenaert.zhang_audenaert
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:56:16.706605+00:00
-- url     : https://prove2.me/theorems/8ebaaeca-126d-492e-b97e-76ceef503c6e
-- title:
--   Theorem 10.7.4 (Zhang–Audenaert): $|H(X)-H(Y)|\le T\log(|\mathcal A|-1)+h_2(T)$, $T=\tfrac12\|p_X-p_Y\|_1$, and the bound is optimal
-- statement:
--   Let $X$ and $Y$ be random variables taking values in a finite (nonempty) alphabet $\mathcal A$, with distributions $p_X$ and $p_Y$, and let $T\equiv\tfrac12\|p_X-p_Y\|_1$ be their normalized classical trace distance. Let $H$ denote entropy and $h_2$ the binary entropy, both in bits. Then:
--
--   1. (10.102) For every pair of distributions $p_X,p_Y$ on $\mathcal A$,
--   $$
--   |H(X)-H(Y)|\le T\log(|\mathcal A|-1)+h_2(T).
--   $$
--   2. The bound is optimal: for every $T\in[0,1]$ (with $|\mathcal A|\ge2$, unless $T=0$) there is a pair of distributions $p_X,p_Y$ on $\mathcal A$ with $\tfrac12\|p_X-p_Y\|_1=T$ and
--   $$
--   |H(X)-H(Y)|=T\log(|\mathcal A|-1)+h_2(T).
--   $$
--
--   This is the sharp uniform continuity bound for Shannon entropy in terms of trace distance; it holds for every $T$, without a case split. Its quantum and conditional analogues (Fannes–Audenaert, Alicki–Fannes–Winter) are used throughout the book's converse proofs.
--
--   **Formalization Note** Logarithms are base $2$; $\log(|\mathcal A|-1)$ uses real subtraction, which gives $\log 0=0$ when $|\mathcal A|=1$ (then $T=0$ for every pair).
--
--   Differences from the source:
--   - reading: saturating the bound for every T ∈ [0, 1] and alphabet size |A| → for every T ∈ [0,1] with |A| ≥ 2 or T = 0; reason: on a one-letter alphabet every pair has T = 0, so T ∈ (0,1] cannot be realized there; T = 0 is still included
--   - encoding: a finite alphabet A → a Fintype α with [Nonempty α]; reason: an empty alphabet carries no distribution, so the bound is vacuous there; the optimality clause needs a distribution to exist
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 10.7.4, eq. (10.102), p. 308; optimality example eqs. (10.124)–(10.126), p. 310

import Mathlib
import Definitions.Def_WildeQIT_entropy
import Definitions.Def_WildeQIT_binaryEntropy
import Definitions.Def_WildeQIT_classicalTraceDist

namespace WildeQIT.ZhangAudenaert

/-- **Theorem 10.7.4 (Zhang–Audenaert).**
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Theorem 10.7.4, (10.102),
p. 308 (optimality example (10.124)–(10.126), p. 310): "Let `X` and `Y` be discrete random
variables taking values in a finite alphabet `𝒜`. Let `p_X` and `p_Y` denote their
distributions, respectively. Then the following bound holds
`|H(X) − H(Y)| ≤ T log(|𝒜| − 1) + h₂(T)`, where `T ≡ (1/2)‖p_X − p_Y‖₁`. Furthermore, this bound
is optimal, meaning that there exists a pair of random variables saturating the bound for every
`T ∈ [0, 1]` and alphabet size `|𝒜|`."

The statement has two parts:
1. the bound, for every pair of distributions `p, q` on `α` (no restriction on `T`);
2. optimality: for every `T ∈ [0, 1]` there are `p, q` on `α` with `(1/2)‖p − q‖₁ = T` and
   equality in the bound. For a one-letter alphabet only `T = 0` is a possible trace distance,
   so this part assumes `|α| ≥ 2` or `T = 0`.

**Formalization Note.** The alphabet is a nonempty finite type `α` (the bound is vacuous on an
empty one, which carries no distribution); entropies are in bits; `log(|𝒜| − 1)` is
`Real.logb 2 ((Fintype.card α : ℝ) − 1)`, with real subtraction, which is `0` when `|α| = 1`
(then `T = 0`). `h₂ = binaryEntropy`, with `h₂(0) = h₂(1) = 0`. -/
theorem zhang_audenaert {α : Type} [Fintype α] [Nonempty α] :
    (∀ p q : FinDist α,
      |entropy p - entropy q| ≤
        (1 / 2) * classicalTraceDist p.prob q.prob * Real.logb 2 ((Fintype.card α : ℝ) - 1) +
          binaryEntropy ((1 / 2) * classicalTraceDist p.prob q.prob)) ∧
      (∀ T : ℝ, 0 ≤ T → T ≤ 1 → (2 ≤ Fintype.card α ∨ T = 0) →
        ∃ p q : FinDist α, (1 / 2) * classicalTraceDist p.prob q.prob = T ∧
          |entropy p - entropy q| =
            T * Real.logb 2 ((Fintype.card α : ℝ) - 1) + binaryEntropy T) := by sorry

end WildeQIT.ZhangAudenaert
