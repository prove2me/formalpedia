-- Prove2me | Theorems.Thm_WildeQIT_ZhangAudenaert_half_traceDist_eq
-- name    : WildeQIT.ZhangAudenaert.half_traceDist_eq
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T17:56:14.161643+00:00
-- url     : https://prove2.me/theorems/691ad309-fb87-43b0-adb4-f8595f9787dd
-- title:
--   Lemma 10.7.1: $\tfrac12\|p-q\|_1=p(A)-q(A)$ for $A=\{x:p(x)\ge q(x)\}$
-- statement:
--   Let $p$ and $q$ be probability distributions on a finite alphabet $\mathcal X$, let $\|p-q\|_1=\sum_x|p(x)-q(x)|$ be their classical trace distance, and let $A\equiv\{x:p(x)\ge q(x)\}$. Then
--
--   $$
--   \tfrac12\|p-q\|_1=p(A)-q(A),
--   $$
--
--   where $p(A)=\sum_{x\in A}p(x)$ and $q(A)=\sum_{x\in A}q(x)$.
--
--   The set $A$ is the optimal binary test for distinguishing $p$ from $q$, and the identity gives the classical trace distance its operational meaning as a bias in success probability.
--
--   Differences from the source: none.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Lemma 10.7.1, eq. (10.93), p. 307

import Mathlib
import Definitions.Def_WildeQIT_FinDist
import Definitions.Def_WildeQIT_classicalTraceDist

namespace WildeQIT.ZhangAudenaert

/-- **Lemma 10.7.1.**
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Lemma 10.7.1, (10.93),
p. 307: "Let `p` and `q` be probability distributions on a finite alphabet `𝒳`. Let
`A ≡ {x : p(x) ≥ q(x)}`. Then `(1/2)‖p − q‖₁ = p(A) − q(A)`, where `p(A) ≡ ∑_{x∈A} p(x)` and
`q(A) ≡ ∑_{x∈A} q(x)`."

**Formalization Note.** `‖p − q‖₁ = classicalTraceDist p.prob q.prob = ∑_x |p(x) − q(x)|`
(Definition 10.7.1). The set `A` is the `Finset` of letters with `q(x) ≤ p(x)`. -/
theorem half_traceDist_eq {α : Type} [Fintype α] (p q : FinDist α) :
    (1 / 2) * classicalTraceDist p.prob q.prob =
      ∑ x ∈ Finset.univ.filter (fun x => q.prob x ≤ p.prob x), p.prob x -
        ∑ x ∈ Finset.univ.filter (fun x => q.prob x ≤ p.prob x), q.prob x := by sorry

end WildeQIT.ZhangAudenaert
