-- Prove2me | Theorems.Thm_PebbleMotion_Trees_theorem_A
-- name    : PebbleMotion.Trees.theorem_A
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T22:38:57.797194+00:00
-- url     : https://prove2.me/theorems/2336478f-48c4-49fe-a25a-dd172025765c
-- title:
--   Theorem A (Kornhauser–Miller–Spirakis) — feasibility with q ≥ 2 blanks
-- statement:
--   Let $2\le q\le N-1$ and $n+q=N$. Let $G$ be a connected graph with $N$ vertices that is not a cycle, and let $P=\{1,\dots,n\}$ be pebbles on $G$. Then the following are equivalent: (1) $G$ has no $q$-isthmus; (2) $(G,P)$ is transitive; (3) every pair of configurations of $P$ on $G$ can be transformed into each other by a finite sequence of moves (the puzzle is feasible).
--
--   The vertex set is any finite type with decidable equality; "not a cycle" is the negation of "connected and every vertex has degree 2".
--
--   Differences from the source:
--   - encoding: G is not a cycle → ¬ (G connected ∧ every vertex has exactly 2 neighbours); reason: for a connected finite graph this is exactly not being the cycle C_N
--   - encoding: a set of n pebbles; configurations V → {0,…,n} → labels Fin (n+1), 0 = blank; moves as (from, to) pairs; reason: same instances
-- source:
--   Nakamigawa and Sakuma, Structural Origins of Cubic Complexity in Pebble Motion, arXiv:2503.20550 (held revision dated 2026-11-03), Theorem A (cited from [KMS84]), p.8, PDF SHA256 efd330453039630e97e2ef1029ef0b2b3ac5a16bd700a2c5fad226582870f412

import Mathlib
import Definitions.Def_PebbleMotion_Trees_Isthmus
import Definitions.Def_PebbleMotion_Trees_Moves

set_option autoImplicit false

namespace PebbleMotion.Trees

theorem theorem_A {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (n q : ℕ)
    (hq : 2 ≤ q) (hqN : q + 1 ≤ Fintype.card V) (hnq : n + q = Fintype.card V)
    (hconn : G.Connected) (hcyc : ¬ IsCycleGraph G) :
    [¬ ∃ I : List V, IsIsthmus G I ∧ I.length = q,
      IsTransitive G n,
      IsFeasiblePuzzle G n].TFAE := by sorry

end PebbleMotion.Trees
