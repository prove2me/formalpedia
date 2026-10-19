-- Prove2me | Theorems.Thm_SandsSauerWoodrow_asymPart_strictOrder
-- name    : SandsSauerWoodrow.asymPart_strictOrder
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-17T06:03:31.125579+00:00
-- url     : https://prove2.me/theorems/b2513254-0539-4696-b111-e1328e8ed281
-- title:
--   The asymmetric part of one colours reachability is a strict partial order
-- statement:
--   This is a step of the proof of Theorem 1 of Sands, Sauer and Woodrow (*On monochromatic paths in edge-coloured digraphs*, J. Combin. Theory Ser. B **33** (1982), 271–275, pp. 271–273), isolated as the strict-order requirement in the mechanized development of Chancelier (arXiv:2604.21376, Lemma 9).
--
--   Let $D$ be a digraph on a set $V$ of vertices whose arcs are coloured, and fix a colour $k$. Write $x \to_k y$ when $y$ is reachable from $x$ along a directed path all of whose arcs have colour $k$, and let
--
--   $$x\,R_k\,y \iff x \to_k y \ \wedge\ \neg\, y \to_k x .$$
--
--   Then $R_k$ is a **strict partial order** on $V$: it is irreflexive, so that no vertex is related to itself, and transitive, so that $x\,R_k\,y$ and $y\,R_k\,z$ give $x\,R_k\,z$.
--
--   This relation is the one whose asymmetric part induces the order on sets of vertices used in the maximality argument of the same theorem; the source paper uses it implicitly, and the mechanized reference states the strict-order property as its Lemma 9.
--
--   **Formalization Note.** The colour is a value of a three-element type, matching the platform module `opg1808_colored_tournaments`; reachability along one colour is its reflexive-transitive closure on the arcs of that colour.
-- source:
--   Proof step of B. Sands, N. Sauer, R. Woodrow, On monochromatic paths in edge-coloured digraphs, J. Combin. Theory Ser. B 33 (1982), no. 3, 271-275, Theorem 1 (pp. 271-273). Order formulation and isolation of the step: J.-P. Chancelier, A formal proof of the Sands-Sauer-Woodrow theorem using the Rocq prover and mathcomp/ssreflect, arXiv:2604.21376, Definition 8 (eq. 4) and Lemma 9.

import Definitions.Def_opg1808_colored_tournaments
import Definitions.Def_SandsSauerWoodrow_OrderOnSets

open OPG1808

universe u

namespace SandsSauerWoodrow

theorem asymPart_strictOrder {V : Type u} (D : Digraph V) (color : ArcColoring V) (k : Fin 3) :
    Irreflexive (asymPart D color k) ∧ Transitive (asymPart D color k) := by sorry

end SandsSauerWoodrow
