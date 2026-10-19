-- Prove2me | Theorems.Thm_SandsSauerWoodrow_leSet_antisymm
-- name    : SandsSauerWoodrow.leSet_antisymm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-17T06:03:32.224623+00:00
-- url     : https://prove2.me/theorems/4a3dd0f8-bf30-48d1-a51f-cde7d5bc720a
-- title:
--   The induced order is antisymmetric on independence-respecting sets
-- statement:
--   This is a step of the proof of Theorem 1 of Sands, Sauer and Woodrow (*On monochromatic paths in edge-coloured digraphs*, J. Combin. Theory Ser. B **33** (1982), 271–275, pp. 271–273), in the form given by Chancelier (arXiv:2604.21376, Definition 2 and Lemma 9).
--
--   Let $R$ be a strict partial order on a set $V$ — irreflexive and transitive — and call a subset $S \subseteq V$ **$R$-independent** when no two of its distinct members are related by $R$ in either direction: for distinct $x, y \in S$, neither $x\,R\,y$ nor $y\,R\,x$. With $\preceq_R$ as above, if two $R$-independent sets satisfy $S \preceq_R T$ and $T \preceq_R S$, then
--
--   $$S = T .$$
--
--   That is, $\preceq_R$ is antisymmetric on the $R$-independent sets. Together with its reflexivity and transitivity this makes the pair of the $R$-independent sets and $\preceq_R$ a partially ordered set, which is what licenses taking a maximal element in the source's argument.
--
--   **Formalization Note.** For the monochromatic relation of the source, $R$-independence is the paper's notion of an independent set of vertices.
-- source:
--   Proof step of B. Sands, N. Sauer, R. Woodrow, On monochromatic paths in edge-coloured digraphs, J. Combin. Theory Ser. B 33 (1982), no. 3, 271-275, Theorem 1 (pp. 271-273). Order formulation and isolation of the step: J.-P. Chancelier, A formal proof of the Sands-Sauer-Woodrow theorem using the Rocq prover and mathcomp/ssreflect, arXiv:2604.21376, Definition 8 (eq. 4) and Lemma 9.

import Definitions.Def_opg1808_colored_tournaments
import Definitions.Def_SandsSauerWoodrow_OrderOnSets

open OPG1808

universe u

namespace SandsSauerWoodrow

theorem leSet_antisymm {V : Type u} {R : V → V → Prop}
    (hirr : Irreflexive R) (htr : Transitive R) {S T : Set V}
    (hS : RelIndep R S) (hT : RelIndep R T) (hST : leSet R S T) (hTS : leSet R T S) :
    S = T := by sorry

end SandsSauerWoodrow
