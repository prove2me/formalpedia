-- Prove2me | Theorems.Thm_TightClock_lemma_6_7
-- name    : TightClock.lemma_6_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T05:06:21.425415+00:00
-- url     : https://prove2.me/theorems/1a26fc2b-47d7-4224-ab22-cf2ff240e762
-- title:
--   Lemma 6.7 — high-moment bound for random splits
-- statement:
--   Let $S$ be a node at depth $r-1$, $1\le r\le L$, fix a state $J$, and let $D$ be a random child of $S$, containing each member of $S$ independently with probability $a$. Then
--
--   $$\mathbb E_D\Big[\Big(\frac{A_D(J)}{A_S(J)}\Big)^{M^r}\Big]\le e^{-hM^r}.$$
--
--   This tail control is what allows a union bound over the enormous number of nodes in the tree.
--
--   **Formalization Note** The exponent $M^r$ is a natural number. The accounts are written on sets, since they depend on a node only through its depth and its bidder set.
--
--   Differences from the source:
--   - encoding: the depth $L$ of the tree, with levels $r=1,\dots,L$ in Instance 11 → the hypothesis `1 ≤ L`; reason: at $L=0$ there are no bidders and $h=a^2B/L$ divides by zero; the page's construction has $L\ge1$
--   - generalization: $S$ a node at depth $r-1$ → $S$ an arbitrary finite set of bidders, with the account formula (6.11) at depth $r-1$; reason: a node enters the page's statement and proof only through its set and depth, so every node's set is an instance; at $r=1$ the only node at depth $0$ is the root, whose set is all bidders, so the Lean also covers sets that are no node's set
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), Lemma 6.7, §6.4, p.42 (PDF p.45)

import Mathlib
import Definitions.Def_TightClock_accountOf
import Definitions.Def_TightClock_thinExpect
import Definitions.Def_TightClock_M

set_option autoImplicit false

namespace TightClock

/-- Lemma 6.7 (High-moment bound for random splits), p.42 (PDF 45), of Afshinmehr et al., manuscript (STOC 2027
submission): for `S` at depth `r − 1`, a fixed state `J` and a random child `D` of `S`,
`E_D[(A_D(J) / A_S(J))^{Mʳ}] ≤ e^{−h Mʳ}`.

**Formalization Note** The child is at depth `r`, and the set is at depth `r − 1`, with `1 ≤ r ≤ L`; the natural
subtraction is exact. -/
theorem lemma_6_7 (q L : ℕ) (hq : 8 ≤ q) (hL : 1 ≤ L) (r : ℕ) (hr1 : 1 ≤ r) (hrL : r ≤ L)
    (S : Finset (Fin (bidderCount q L))) (J : State q L) :
    thinExpect q S (fun D => (accountOf q L r D J / accountOf q L (r - 1) S J) ^ ((M q L) ^ r)) ≤
      Real.exp (-(fee q L * ((M q L : ℝ) ^ r))) := by sorry

end TightClock
