-- Prove2me | Theorems.Thm_SandsSauerWoodrow_leSet_trans
-- name    : SandsSauerWoodrow.leSet_trans
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-17T06:03:32.607638+00:00
-- url     : https://prove2.me/theorems/27712a70-0e55-406f-af65-28a8acf10d2e
-- title:
--   The order a transitive relation induces on sets is transitive
-- statement:
--   This is a step of the proof of Theorem 1 of Sands, Sauer and Woodrow (*On monochromatic paths in edge-coloured digraphs*, J. Combin. Theory Ser. B **33** (1982), 271–275, pp. 271–273), in the form given by Chancelier (arXiv:2604.21376, Definition 8 and Lemma 9).
--
--   Let $R$ be a relation on a set $V$, and let it induce an order on subsets of $V$ by
--
--   $$S \preceq_R T \iff \forall x \in S,\ \exists y \in T,\ x = y \ \vee\ x\,R\,y .$$
--
--   If $R$ is transitive, then so is $\preceq_R$: from $S \preceq_R T$ and $T \preceq_R U$ follows $S \preceq_R U$.
--
--   The order on sets is the one the maximality argument of the source theorem takes a maximal element of, so its order-theoretic laws are what make that argument available.
--
--   **Formalization Note.** $\preceq_R$ is equation (4) of the mechanized reference; transitivity is one of the two laws that make it a partial order on independent sets there.
-- source:
--   Proof step of B. Sands, N. Sauer, R. Woodrow, On monochromatic paths in edge-coloured digraphs, J. Combin. Theory Ser. B 33 (1982), no. 3, 271-275, Theorem 1 (pp. 271-273). Order formulation and isolation of the step: J.-P. Chancelier, A formal proof of the Sands-Sauer-Woodrow theorem using the Rocq prover and mathcomp/ssreflect, arXiv:2604.21376, Definition 8 (eq. 4) and Lemma 9.

import Definitions.Def_opg1808_colored_tournaments
import Definitions.Def_SandsSauerWoodrow_OrderOnSets

open OPG1808

universe u

namespace SandsSauerWoodrow

theorem leSet_trans {V : Type u} {R : V → V → Prop} (hR : Transitive R) :
    Transitive (leSet R) := by sorry

end SandsSauerWoodrow
