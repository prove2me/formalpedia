-- Prove2me | Theorems.Thm_SplayDynOpt_lemma_17
-- name    : SplayDynOpt.lemma_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:58:24.520262+00:00
-- url     : https://prove2.me/theorems/c4943d37-90be-4a70-bf64-c9e939f68a11
-- title:
--   Lemma 17 — bends created and removed by one splay (corrected: removal count up to an additive O(1))
-- statement:
--   For every $k$ there is a constant $c$ such that the following holds. Let $S$ and $T$ be binary search trees on $[n]$, with $T$ being $k$-ribless and with the accessed key $x$ at the root of $T$. Take ranks to be depths in $T$, and let $S'$ be the result of splaying $x$ in $S$. Then:
--
--   1. the number of bends created is at most $c$ plus the number of zig-zigs of this splay:
--   $$
--   |\operatorname{bends}(S')\setminus\operatorname{bends}(S)|\le c+\#\text{zig-zigs};
--   $$
--   2. the number of zig-zags is at most the number of bends removed plus $c$:
--   $$
--   \#\text{zig-zags}\le|\operatorname{bends}(S)\setminus\operatorname{bends}(S')|+c .
--   $$
--
--   Over a whole access sequence this bounds the zig-zags by the zig-zigs and the number of bends ever created.
--
--   Differences from the source:
--   - correction: the number of bends removed by a splay is at least #zig-zags → #zig-zags ≤ |bends(S) ∖ bends(S′)| + c, comparing the bend sets before and after; reason: read on the bend sets before and after the splay, the printed clause is false, and the paper's count is event-level, through an intermediate rank assignment for x⁻, x⁺ (p.31) that has no meaning at the endpoints. Counterexample satisfying every assumption: with T = 4(2(1,3),5(nil,6)), which is 1-ribless, and S = 1(nil,6(5(3(2,4),nil),nil)), splaying 4 does 2 zig-zags and removes one bend (verification file). The c comes from the O(1) junctions that restore the true ranks
--   - reading: bends created by a splay, O(1) + #zig-zigs → |bends(S′) ∖ bends(S)| ≤ c + #zig-zigs; reason: creation read as set difference; the event-level count bounds it
--   - generalization: T*, the nearly optimal tree → every k-ribless binary search tree T with root x, and c depending on k only; reason: the proof uses only riblessness, through Corollary 3; T* at an access time is one such tree
-- source:
--   Chmel et al., Splay trees are almost dynamically optimal, arXiv:2607.18498 (version of 2026-11-02, sha256 6881e83c…), Lemma 17, p.31 (setting §5.4.1, p.28)

import Mathlib
import Definitions.Def_SplayDynOpt_splayCost
import Definitions.Def_SplayDynOpt_kRibless
import Definitions.Def_SplayDynOpt_extRank
import Definitions.Def_SplayDynOpt_bends

set_option autoImplicit false

namespace SplayDynOpt

/-- **Lemma 17 (corrected: removal count up to an additive `O(1)`).** For every `k` there is a constant `c` such that: let `S` (the splay tree) and `T`
(the nearly optimal tree, `k`-ribless) be BSTs on `[n]` with the accessed key `x` at the root of
`T`, ranks being depths in `T`, and let `S'` be the result of splaying `x` in `S`. Then
1. the number of bends created, `|bends(S') ∖ bends(S)|`, is at most `c + #zig-zigs`;
2. `#zig-zags ≤ |bends(S) ∖ bends(S')| + c` (bends removed).

Chmel, Haeupler, Hladík, Koucký, Roeyskoe, Rozhoň, Sladký, Tarjan, *Splay trees are almost
dynamically optimal*, arXiv:2607.18498 (version of 2026-11-02, sha256 6881e83c…), Lemma 17, p.31 (setting §5.4.1, p.28).

**Formalization Note.** Bends are compared as sets before and after the splay. In the paper's
proof the lower node of every zig-zag is a bend before the splay; restoring the true ranks of
`x⁻, x⁺` makes `O(1)` junctions, which may turn `O(1)` of those nodes into bends again, so the
set-based removal count carries the additive constant `c`. Without it the printed clause is
false: `T = 4(2(1,3),5(nil,6))` is `1`-ribless with root `4`, `S = 1(nil,6(5(3(2,4),nil),nil))`,
and splaying `4` does two zig-zags while the bend set goes from `{3, 6}` to `{3}`. The statement is made for every
`k`-ribless `T`; `c` depends on `k` only. -/
theorem lemma_17 :
    ∀ k : ℕ, ∃ c : ℕ, ∀ n : ℕ, ∀ S T : BinaryTree ℕ, ∀ x : ℕ, IsBSTOn n S → IsBSTOn n T →
      kRibless k T → root T = some x →
        (bends (extRank T) (splay x S).1 \ bends (extRank T) S).card ≤ c + (splay x S).2.zigzig ∧
        (splay x S).2.zigzag ≤ (bends (extRank T) S \ bends (extRank T) (splay x S).1).card + c := by sorry

end SplayDynOpt
