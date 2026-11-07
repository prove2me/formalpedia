-- Prove2me | Theorems.Thm_SplayDynOpt_corollary_3
-- name    : SplayDynOpt.corollary_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:57:27.093208+00:00
-- url     : https://prove2.me/theorems/2aadb983-c3c0-4d64-875d-91416a6ecedd
-- title:
--   Corollary 3 — the depths of $x$, $\bot_{x-1}$, $\bot_x$ differ by $O(1)$
-- statement:
--   For every $k$ there is a constant $c$ such that for every $k$-ribless binary search tree $T$ on $[n]$ and every key $x\in[n]$, the depths in $T$ of $x$, $\bot_{x-1}$ and $\bot_x$ (with null nodes added) differ pairwise by at most $c$:
--   $$
--   |\operatorname{rank}(x)-\operatorname{rank}(\bot_{x-1})|\le c,\quad |\operatorname{rank}(x)-\operatorname{rank}(\bot_x)|\le c,\quad |\operatorname{rank}(\bot_{x-1})-\operatorname{rank}(\bot_x)|\le c.
--   $$
--
--   This is why riblessness is needed: the neighbours of an accessed key in symmetric order have rank $O(1)$ when the key is at the root.
--
--   Differences from the source:
--   - generalization: T*, the nearly optimal tree of Theorem 2 → every k-ribless binary search tree on [n], with c depending on k only; reason: T* is k-ribless, so this specializes to the printed statement; the proof uses riblessness only
--   - encoding: depths of x, ⊥_{x−1}, ⊥_x → extRank T at positions 2x − 1, 2x − 2, 2x; reason: null nodes numbered in symmetric order; same quantities
-- source:
--   Chmel et al., Splay trees are almost dynamically optimal, arXiv:2607.18498 (version of 2026-11-02, sha256 6881e83c…), Corollary 3, p.15

import Mathlib
import Definitions.Def_SplayDynOpt_IsBSTOn
import Definitions.Def_SplayDynOpt_kRibless
import Definitions.Def_SplayDynOpt_extRank

set_option autoImplicit false

namespace SplayDynOpt

/-- **Corollary 3.** For every `k` there is a constant `c` such that in every `k`-ribless BST `T`
on `[n]` (with null nodes added), for every key `x ∈ [n]`, the depths of `x`, `⊥_{x−1}` and
`⊥_x` differ pairwise by at most `c`.

Chmel, Haeupler, Hladík, Koucký, Roeyskoe, Rozhoň, Sladký, Tarjan, *Splay trees are almost
dynamically optimal*, arXiv:2607.18498 (version of 2026-11-02, sha256 6881e83c…), Corollary 3, p.15.

**Formalization Note.** Depths with null nodes are `extRank T` at the external positions
`2x − 1` (key `x`), `2x − 2` (`⊥_{x−1}`) and `2x` (`⊥_x`). The statement is made for every
`k`-ribless BST, not only for the nearly optimal tree `T*`; `c` depends on `k` only. -/
theorem corollary_3 :
    ∀ k : ℕ, ∃ c : ℕ, ∀ n : ℕ, ∀ T : BinaryTree ℕ, IsBSTOn n T → kRibless k T →
      ∀ x ∈ Finset.Icc 1 n,
        |(extRank T (2 * x - 1) : ℤ) - extRank T (2 * x - 2)| ≤ c ∧
        |(extRank T (2 * x - 1) : ℤ) - extRank T (2 * x)| ≤ c ∧
        |(extRank T (2 * x - 2) : ℤ) - extRank T (2 * x)| ≤ c := by sorry

end SplayDynOpt
