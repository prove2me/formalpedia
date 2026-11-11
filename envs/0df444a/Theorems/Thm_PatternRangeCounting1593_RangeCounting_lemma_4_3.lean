-- Prove2me | Theorems.Thm_PatternRangeCounting1593_RangeCounting_lemma_4_3
-- name    : PatternRangeCounting1593.RangeCounting.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:12:03.752097+00:00
-- url     : https://prove2.me/theorems/33de7e41-d78a-4b07-8167-27a676e0a07e
-- title:
--   Lemma 4.3 — laminar projection onto anchor columns
-- statement:
--   Let $\tau$ be a permutation of length $m$ with nested row and column divisions at levels $0,\dots,\ell$, let $a\le\ell$, and let $R$ be a row block at level $a$ with level-$i$ ancestors $R_i$. Let $S_R$ be the set of column blocks $C$ at levels $i\le a$ whose cell $C\times R_i$ is occupied, and for $C\in S_R$ let $\lambda(C)$, $\eta(C)$ be the one-based ranks of the first and last level-$a$ column blocks contained in $C$. List the distinct endpoints $\lambda(C)$ and $\eta(C)+1$ ($C\in S_R$) in increasing order. For any two consecutive endpoints $b<b'$:
--
--   1. there is one $C^\star\in S_R$ that, for every rank $b\le z<b'$, covers $z$ (that is, $\lambda(C^\star)\le z\le\eta(C^\star)$) and is the deepest node of $S_R$ covering $z$: every other $C\in S_R$ covering $z$ lies at a strictly smaller level; hence its cell, and its continuation state, is the same throughout the interval;
--   2. the number of such intervals, one less than the number of endpoints, is at most $2|S_R|$.
--
--   This is what allows one predecessor search over the endpoints to locate the gateway.
--
--   Differences from the source:
--   - generalization: the anchor level a of §4.1 → any level a ≤ ℓ of any valid pair of nested division chains; reason: the argument uses only the nesting of the divisions; the source's case is a = anchor level
--   - encoding: its cell therefore has the same continuation state → a single node C⋆ serves the whole interval, so its cell and state are literally the same; reason: the state is a function of the cell
--   - encoding: there are at most 2|S_R| such intervals → (number of endpoints) − 1 ≤ 2|S_R|; reason: consecutive pairs of a sorted list
-- source:
--   Sankardeep Chakraborty, STOC 2027 submission #1593 (October 2026), Lemma 4.3, printed p. 16 (PDF p. 17)

import Mathlib
import Definitions.Def_PatternRangeCounting1593_RangeCounting_Perm
import Definitions.Def_PatternRangeCounting1593_RangeCounting_Machine
import Definitions.Def_PatternRangeCounting1593_RangeCounting_Hierarchy
import Definitions.Def_PatternRangeCounting1593_RangeCounting_KOInterface
import Definitions.Def_PatternRangeCounting1593_RangeCounting_IndexSpecs
set_option autoImplicit false
open Filter Topology
open Classical

namespace PatternRangeCounting1593.RangeCounting

/-- Lemma 4.3 (Laminar projection onto anchor columns). -/
theorem lemma_4_3 {m : ℕ} (τ : Equiv.Perm (Fin m)) (Hd : Hierarchy) (hHd : Hd.Valid m)
    (a : ℕ) (ha : a ≤ Hd.ell) (r : ℕ) (hr : r < numBlocks Hd.rb m a)
    (b b' : ℕ) (hb : b ∈ endpoints τ Hd a r) (hb' : b' ∈ endpoints τ Hd a r) (hbb' : b < b')
    (hcons : ∀ e ∈ endpoints τ Hd a r, ¬ (b < e ∧ e < b')) :
    (∃ ic ∈ markedSet τ Hd a r, ∀ z, b ≤ z → z < b' →
        (lam Hd m a ic.1 ic.2 ≤ z ∧ z ≤ eta Hd m a ic.1 ic.2) ∧
        ∀ jc ∈ markedSet τ Hd a r, lam Hd m a jc.1 jc.2 ≤ z → z ≤ eta Hd m a jc.1 jc.2 →
          jc.1 < ic.1 ∨ jc = ic) ∧
    (endpoints τ Hd a r).card - 1 ≤ 2 * (markedSet τ Hd a r).card := by sorry

end PatternRangeCounting1593.RangeCounting
