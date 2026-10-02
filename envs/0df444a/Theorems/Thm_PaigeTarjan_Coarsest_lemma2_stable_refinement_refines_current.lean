-- Prove2me | Theorems.Thm_PaigeTarjan_Coarsest_lemma2_stable_refinement_refines_current
-- name    : PaigeTarjan.Coarsest.lemma2_stable_refinement_refines_current
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T17:49:28.455972+00:00
-- url     : https://prove2.me/theorems/97bc30d3-6d54-4091-82f9-039b1b0da9cd
-- title:
--   Lemma 2, p. 979 — every stable refinement of P refines the current partition Q
-- statement:
--   Let $E$ be a relation on a finite set $U$ and $P$ a partition of $U$. Consider any run $Q_0 = P, Q_1, \dots, Q_K$ of the naïve refinement algorithm, in which each $Q_{j+1} = \mathrm{split}(S_j, Q_j)$ for a set $S_j$ that is a union of blocks of $Q_j$ and a splitter of $Q_j$. If $R$ is a stable partition of $U$ that refines $P$, then
--   $$R \text{ is a refinement of } Q_j \quad \text{for every } j = 0, 1, \dots, K.$$
--
--   In particular any coarsest stable refinement of $P$ refines every partition the algorithm produces, which is the form printed in the paper. Lemma 2 is the invariant from which the correctness of the naïve algorithm (Theorem 2) follows.
--
--   **Formalization Note** The paper states the invariant for "any coarsest stable refinement of the initial partition $P$"; its proof never uses coarseness, and the proof of Theorem 2 applies it to "any stable refinement". The statement here is that stronger form, which implies the printed one.
-- source:
--   Paige, Tarjan, Three Partition Refinement Algorithms, SIAM J. Comput. 16 (1987), p. 979, Lemma 2

import Mathlib
import Definitions.Def_PaigeTarjan_Coarsest_Basic
import Definitions.Def_PaigeTarjan_Coarsest_Algorithms

namespace PaigeTarjan.Coarsest

/-- Lemma 2, p. 979: the naïve refinement algorithm maintains the invariant that any stable
refinement `R` of the initial partition `P` (in particular any coarsest stable refinement of `P`)
is also a refinement of the current partition `Q`. -/
theorem lemma2_stable_refinement_refines_current {U : Type*} [Fintype U] [DecidableEq U]
    (E : U → U → Prop) [DecidableRel E] (P : Finset (Finset U)) (hP : IsPartition P)
    (K : ℕ) (Qs : Fin (K + 1) → Finset (Finset U)) (hrun : IsNaiveRun E P K Qs)
    (R : Finset (Finset U)) (hR : IsPartition R) (hRP : Refines R P) (hRs : Stable E R) :
    ∀ j : Fin (K + 1), Refines R (Qs j) := by sorry

end PaigeTarjan.Coarsest
