-- Prove2me | Theorems.Thm_StableMSR_Recovery_DecompositionSearch_tight_block_progress
-- name    : StableMSR.Recovery.DecompositionSearch.tight_block_progress
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-14T17:21:05.858057+00:00
-- url     : https://prove2.me/theorems/dd20c255-deeb-424a-9d73-e2d40d07663e
-- title:
--   Progress and exact child accounting in tight-boundary decomposition search
-- statement:
--   Let a finite graph have a width-$w$ tree decomposition. Let $C$ be a component of $G-S$ with exact external boundary $S=N_G(C)$, and suppose some bag contains $S$. There is a candidate bag $S\subseteq B\subseteq S\cup C$ with at most $w+1$ vertices that meets $C$ and is contained in an original bag. Its recursive child regions, the components $D$ of $G-B$ contained in $C$, satisfy the exact accounting identity
--
--   $$|B\cap C|+\sum_D |D|=|C|.$$
--
--   Each child is a component after deleting its own exact boundary, that boundary is contained in $B$ and in an original bag, and
--
--   $$|N_G(D)|\le w,\qquad |D|<|C|.$$
--
--   Also $|S|\le w$. This proves closure and strict progress of the intended finite-state decomposition search. The complete search recurrence, its reconstructed tree, and its instruction-level implementation are separate obligations.
-- source:
--   Supporting lemma for Prove2Me Exact Sum-of-Radii Clustering under Any Constant Stability; tight-boundary connected-component decomposition search and finite cardinality charging.

import Definitions.Def_StableMSR_TightBlockSearch
open StableMSR.Recovery.DecompositionSearch StableMSR.Recovery.Havens
open scoped BigOperators

theorem StableMSR.Recovery.DecompositionSearch.tight_block_progress {V : Type} [Fintype V] [DecidableEq V] {T : Type} [Fintype T] [DecidableEq T]
    {G : SimpleGraph V} {tree : SimpleGraph T} {bags : T → Finset V}
    (htd : RobertsonSeymour1986.GM5.IsTreeDecomposition G tree bags)
    (S C : Finset V) (w : ℕ) (hC : IsFlap G S C)
    (htight : boundary G C = S) (hroot : ∃ r, S ⊆ bags r)
    (hwidth : ∀ t, (bags t).card ≤ w+1) :
    ∃ B : Finset V,
      S ⊆ B ∧ B ⊆ S ∪ C ∧ B.card ≤ w+1 ∧ (B ∩ C).Nonempty ∧ S.card ≤ w ∧
      (∃ t, B ⊆ bags t) ∧
      (B ∩ C).card + (∑ D ∈ children G B C, D.card) = C.card ∧
      ∀ D ∈ children G B C,
        IsFlap G (boundary G D) D ∧ boundary G D ⊆ B ∧
        (boundary G D).card ≤ w ∧ D.card < C.card ∧
        ∃ r, boundary G D ⊆ bags r := by sorry
