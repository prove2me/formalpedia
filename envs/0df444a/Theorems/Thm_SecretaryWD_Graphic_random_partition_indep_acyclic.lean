-- Prove2me | Theorems.Thm_SecretaryWD_Graphic_random_partition_indep_acyclic
-- name    : SecretaryWD.Graphic.random_partition_indep_acyclic
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:27:01.081374+00:00
-- url     : https://prove2.me/theorems/29320ba9-1a1f-4c4f-bc44-c05361b84646
-- title:
--   Lemma 5.3 (independence) — the random partition is a partition matroid whose independent sets are forests
-- statement:
--   Let $G$ be a finite simple graph with edge set $E$, and let $P$ be any outcome of the random partition of Lemma 5.3 (any family of parts with positive probability). Then
--
--   1. $P$ is a partition of a subset of $E$: its parts are nonempty, pairwise disjoint, and contained in $E$;
--   2. every set $S$ that is independent in the partition matroid of $P$ (each element of $S$ in some part, at most one element of $S$ per part) is acyclic.
--
--   This is the second bullet of Definition 5.1 for the construction of Lemma 5.3. The paper argues it as follows: picking one bichromatic edge incident on each red node gives a forest, and the union of such a forest with a forest of blue-blue edges is still a forest. Together with the expectation bound it gives the $3$-partition property.
--
--   **Formalization Note.** The claim is for every partition in the support, not on average.
-- source:
--   Babaioff, Dinitz, Gupta, Immorlica and Talwar, Secretary Problems: Weights and Discounts, SODA 2009 (authors' version), p. 9, proof of Lemma 5.3 ("It is easy to see that picking one bichromatic edge ...")

import Mathlib
import Definitions.Def_SecretaryWD_Graphic_GraphicMatroid
import Definitions.Def_SecretaryWD_Graphic_RandomPartition

namespace SecretaryWD.Graphic
theorem random_partition_indep_acyclic {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∀ P ∈ (partitionPMF G.edgeFinset).support,
      IsPartitionOf G.edgeFinset P ∧
        ∀ S : Finset (Sym2 V), IsPartIndep P S → IsAcyclicSet S := by sorry
end SecretaryWD.Graphic
