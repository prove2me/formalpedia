-- Prove2me | Theorems.Thm_SecretaryWD_Graphic_partition_secretary_competitive
-- name    : SecretaryWD.Graphic.partition_secretary_competitive
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:27:44.035992+00:00
-- url     : https://prove2.me/theorems/66a83275-f5f6-4afe-bf6d-f84cbe714221
-- title:
--   Theorem 5.4 (first clause) — e-competitive algorithm on partition matroids
-- statement:
--   Let $E$ be a finite set of edges and let $P$ be a partition of a subset of $E$: a finite family of nonempty, pairwise disjoint parts contained in $E$. Let $v\ge 0$ be edge values. Run the classical secretary rule separately on the arrivals of each part, with the edges of $E$ arriving in a uniformly random order $\pi$. Then
--
--   1. for every order $\pi$, the output is independent in the partition matroid: every selected edge lies in a part, and at most one edge is selected from each part;
--   2. the expected value of the output is at least a $1/e$ fraction of the max-weight base of the partition matroid:
--   $$\sum_{p\in P}\max_{e\in p} v(e)\;\le\; e\cdot \frac{1}{|E|!}\sum_\pi \mathrm{ALG}(P,\pi).$$
--
--   This is the first clause of Theorem 5.4: on partition matroids there is an $e$-competitive algorithm for the matroid secretary problem. Combined with an $\alpha$-partition property it yields an $e\alpha$-competitive algorithm.
--
--   **Formalization Note.** The partition is fixed (deterministic) here. The competitive ratio is stated multiplicatively. Ties between equal values are broken by a fixed enumeration of $E$.
-- source:
--   Babaioff, Dinitz, Gupta, Immorlica and Talwar, Secretary Problems: Weights and Discounts, SODA 2009 (authors' version), pp. 9-10, Theorem 5.4 (first clause) and its proof

import Mathlib
import Definitions.Def_SecretaryWD_Graphic_PartitionSecretary

namespace SecretaryWD.Graphic
theorem partition_secretary_competitive {V : Type*} [Fintype V] [DecidableEq V]
    (E : Finset (Sym2 V)) (P : Finset (Finset (Sym2 V))) (hP : IsPartitionOf E P)
    (v : Sym2 V → ℝ) (hv : ∀ e, 0 ≤ v e) :
    (∀ π : Equiv.Perm (Fin E.card), IsPartIndep P (partitionSecretaryOutput E v P π)) ∧
      partitionValue P v ≤
        Real.exp 1 * SecretaryWD.DiscUpper.uniformAvg fun π => partitionSecretaryValue E v P π := by sorry
end SecretaryWD.Graphic
