-- Prove2me | Theorems.Thm_SplayDynOpt_lemma_13
-- name    : SplayDynOpt.lemma_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:58:25.396407+00:00
-- url     : https://prove2.me/theorems/bb64026d-abce-480d-b052-15fbaa251987
-- title:
--   Lemma 13 — a rotation of $T^*$ causes $O(1)$ junctions and creates $O(1)$ bends
-- statement:
--   For every $k$ there is a constant $c$ such that the following holds. Let $S$ and $T$ be binary search trees on $[n]$, and let $T'$ be obtained from $T$ by one rotation of a key of depth at most $k$. Replace the ranks of the external nodes of $S$, from depths in $T$ to depths in $T'$. Then the number of heavy-path junctions in $S$ is at most $c$, and so is the number of bends created:
--   $$
--   |\operatorname{junctions}(\operatorname{rk}_T,\operatorname{rk}_{T'},S)|\le c,\qquad |\operatorname{bends}(\operatorname{rk}_{T'},S)\setminus\operatorname{bends}(\operatorname{rk}_T,S)|\le c .
--   $$
--
--   Combined with the bound on bends created by splays, this is what limits the number of zig-zags.
--
--   Differences from the source:
--   - generalization: T*, the nearly optimal tree, ribless of logarithmic depth → every binary search tree T on [n], with c depending on the rotation depth bound k only; reason: the proof uses only the rotation depth (Lemma 12, p.25), and T* is one such tree
--   - reading: O(1) junctions due to a rotation; each rotation creates O(1) bends → junctions as nodes whose heavy outgoing edge differs under the two rank functions; bends created as the set difference after minus before; reason: the formal definition on p.22 and the before/after reading of creation
-- source:
--   Chmel et al., Splay trees are almost dynamically optimal, arXiv:2607.18498 (version of 2026-11-02, sha256 6881e83c…), Lemma 13, p.26 (segments and Lemma 12, p.25; Lemma 11, p.24)

import Mathlib
import Definitions.Def_SplayDynOpt_rotateAt
import Definitions.Def_SplayDynOpt_extRank
import Definitions.Def_SplayDynOpt_bends

set_option autoImplicit false

namespace SplayDynOpt

/-- **Lemma 13.** For every `k` there is a constant `c` such that: if `S` (the splay tree) and `T`
(the nearly optimal tree) are BSTs on `[n]` and `T'` is obtained from `T` by one rotation of a key
of depth at most `k`, then changing the ranks from depths in `T` to depths in `T'` causes at most
`c` heavy-path junctions in `S`, and creates at most `c` bends of `S`.

Chmel, Haeupler, Hladík, Koucký, Roeyskoe, Rozhoň, Sladký, Tarjan, *Splay trees are almost
dynamically optimal*, arXiv:2607.18498 (version of 2026-11-02, sha256 6881e83c…), Lemma 13, p.26.

**Formalization Note.** Ranks are `extRank T` before and `extRank T'` after the rotation; the
splay tree `S` does not change. "Junctions" are the internal nodes of `S` whose set of heavy
outgoing edges changes; "bends created" are the bends after the rotation that were not bends
before. "Rotations at constant depth" is a rotation of a key of depth `≤ k`, and `c` depends on
`k` only (riblessness and the depth bound of `T*` are not needed). -/
theorem lemma_13 :
    ∀ k : ℕ, ∃ c : ℕ, ∀ n : ℕ, ∀ S T T' : BinaryTree ℕ, IsBSTOn n S → IsBSTOn n T →
      IsRotationWithin k T T' →
        (junctions (extRank T) (extRank T') S).card ≤ c ∧
        (bends (extRank T') S \ bends (extRank T) S).card ≤ c := by sorry

end SplayDynOpt
