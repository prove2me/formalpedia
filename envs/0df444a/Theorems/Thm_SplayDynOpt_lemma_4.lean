-- Prove2me | Theorems.Thm_SplayDynOpt_lemma_4
-- name    : SplayDynOpt.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:57:27.32421+00:00
-- url     : https://prove2.me/theorems/502f07c5-388c-4d64-8818-748c04dd4254
-- title:
--   Lemma 4 — the minimum-rank external node of an interval is unique
-- statement:
--   Let $T$ be a binary search tree on $[n]$, with external nodes numbered $0,\dots,2n$ in symmetric order and ranks given by depths in $T$ with null nodes. For every interval $[a,b]$ with $0\le a\le b\le 2n$ there is a unique position $v\in[a,b]$ such that
--   $$
--   \operatorname{rank}(v)\le\operatorname{rank}(w)\quad\text{for all }w\in[a,b].
--   $$
--
--   It follows that every internal node of the splay tree has exactly one outgoing heavy edge, so heavy paths are indeed paths.
--
--   Differences from the source:
--   - encoding: a consecutive interval [a, b] of external nodes in symmetric order → natural numbers a ≤ b ≤ 2n as positions, with ∃! for the minimizer; reason: the external nodes are numbered 0,…,2n; same instances
-- source:
--   Chmel et al., Splay trees are almost dynamically optimal, arXiv:2607.18498 (version of 2026-11-02, sha256 6881e83c…), Lemma 4, p.16

import Mathlib
import Definitions.Def_SplayDynOpt_IsBSTOn
import Definitions.Def_SplayDynOpt_extRank

set_option autoImplicit false

namespace SplayDynOpt

/-- **Lemma 4.** For every BST `T*` on `[n]` and every interval `[a, b]` of consecutive external
positions `0 ≤ a ≤ b ≤ 2n` (in symmetric order), there is a unique position `v ∈ [a, b]` of
minimum rank.

Chmel, Haeupler, Hladík, Koucký, Roeyskoe, Rozhoň, Sladký, Tarjan, *Splay trees are almost
dynamically optimal*, arXiv:2607.18498 (version of 2026-11-02, sha256 6881e83c…), Lemma 4, p.16.

**Formalization Note.** The external nodes of the splay tree are the keys `1, …, n` and the null
nodes `⊥₀, …, ⊥ₙ`, numbered in symmetric order `0, …, 2n`; ranks are depths in `T*` with null
nodes (`extRank`). Uniqueness of the minimizer is `∃!`. -/
theorem lemma_4 :
    ∀ n : ℕ, ∀ T : BinaryTree ℕ, IsBSTOn n T → ∀ a b : ℕ, a ≤ b → b ≤ 2 * n →
      ∃! v : ℕ, a ≤ v ∧ v ≤ b ∧ ∀ w : ℕ, a ≤ w → w ≤ b → extRank T v ≤ extRank T w := by sorry

end SplayDynOpt
