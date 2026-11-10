-- Prove2me | Theorems.Thm_SmallClassesNeighbourhood_Linear_rigid_core
-- name    : SmallClassesNeighbourhood.Linear.rigid_core
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T16:35:04.123052+00:00
-- url     : https://prove2.me/theorems/9872080e-e947-4065-b76d-f5389f658439
-- title:
--   Theorem 16 — core with few automorphisms
-- statement:
--   For all sufficiently large integers C_0, set C=C_0^4. Let F have nonempty bipartite parts A,B, with B A-diverse, |B|≥C|A|, and both minimality conditions (M1),(M2). There exist A′⊆A and B″⊆B′⊆B and a positive integer n′ such that
--
--   $$|A'|\le n',\quad |B'|=C_0n',\quad |B''|\le3n',\quad B'\setminus B''\text{ is }A'\text{-diverse},\quad |Aut(F[A',B''])|\le C_0^{100n'}.$$
--
--   The automorphism group is uncoloured. This core theorem supplies the structural target used by the headline theorem; the exact equality for |B′| is retained.
--
--   Differences from the source:
--   - encoding: finite graphs and named vertex subsets → finite ambient carriers with cores on the subtype A ∪ B; reason: isolated padding is ignored; restriction to the union recovers exactly the source graph, including every uncoloured automorphism
--   - encoding: sufficiently large integer parameters → one existential positive natural threshold before every parameter and graph; reason: this is the uniform eventual meaning of sufficiently large, with no instance-dependent threshold
-- source:
--   John Sylvester, Viktor Zamaraev, Maksim Zhukovskii, STOC 2027 submission #1126 (October 2026), Theorem 16, printed p. 12 (PDF p. 13)

import Definitions.Def_SmallClassesNeighbourhood_Linear_graphBasics

namespace SmallClassesNeighbourhood.Linear

theorem rigid_core :
    ∃ L : ℕ, 1 ≤ L ∧ ∀ C0 : ℕ, L ≤ C0 →
      ∀ (V : Type) [Fintype V] [DecidableEq V] (F : SimpleGraph V) (A B : Finset V),
      MinimalPair (C0 ^ 4) F A B →
      ∃ (A' B' Bcore : Finset V) (n' : ℕ), A' ⊆ A ∧ B' ⊆ B ∧ Bcore ⊆ B' ∧
        0 < n' ∧ A'.card ≤ n' ∧ B'.card = C0 * n' ∧ Bcore.card ≤ 3 * n' ∧
        Diverse F A' (B' \ Bcore) ∧ autCount F A' Bcore ≤ C0 ^ (100 * n') := by sorry

end SmallClassesNeighbourhood.Linear
