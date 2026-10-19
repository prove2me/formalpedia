-- Prove2me | Theorems.Thm_SandsSauerWoodrow_InFam_nonempty
-- name    : SandsSauerWoodrow.InFam_nonempty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-17T23:27:36.876981+00:00
-- url     : https://prove2.me/theorems/77fe613a-9b20-4cc8-9d2c-0b6c4d4b0f88
-- title:
--   The family of the maximality argument is nonempty
-- statement:
--   This is the nonemptiness step of the proof of Theorem 1 of Sands, Sauer and Woodrow (*On monochromatic paths in edge-coloured digraphs*, J. Combin. Theory Ser. B **33** (1982), 271–275, pp. 271–273), isolated as Lemma 11 of Chancelier (arXiv:2604.21376).
--
--   Let $D$ be a digraph on a nonempty set $V$ of vertices whose arcs are coloured, and let $R$ be the asymmetric part of reachability along the first colour: $x\,R\,y$ when $y$ is reachable from $x$ along a directed path of that colour and $x$ is not reachable from $y$ along such a path. Suppose $R$ has no infinite outward path — there is no injective sequence of vertices whose consecutive pairs are all related by $R$.
--
--   Then some singleton belongs to the family $\mathcal{S}$ of the source's maximality argument: there is a vertex $v$ such that $\{v\}$ is nonempty and monochromatically independent, and every vertex reachable from $v$ along the first colour is reached from $v$ by a monochromatic path in the reverse direction — that is, $v$ reaches $y$ along the first colour only if $y$ reaches $v$ along it.
--
--   This supplies the starting point of the maximality argument: with a nonempty family and the chain condition, a maximal element exists.
--
--   **Formalization Note.** The family is that of the platform definition `InFam`; the first colour is colour $0$ of the three-valued colouring and the second is colour $1$. Nonemptiness of the vertex set is required, since the vertex $v$ must be exhibited.
-- source:
--   Proof step of B. Sands, N. Sauer, R. Woodrow, On monochromatic paths in edge-coloured digraphs, J. Combin. Theory Ser. B 33 (1982), no. 3, 271-275, Theorem 1 (pp. 271-273). Formulation: J.-P. Chancelier, A formal proof of the Sands-Sauer-Woodrow theorem using the Rocq prover and mathcomp/ssreflect, arXiv:2604.21376, §5-§6.

import Definitions.Def_opg1808_colored_tournaments
import Definitions.Def_SandsSauerWoodrow_OrderOnSets
import Definitions.Def_SandsSauerWoodrow_NoInfinitePath

open OPG1808

universe u

namespace SandsSauerWoodrow

theorem InFam_nonempty {V : Type u} [Nonempty V] (D : Digraph V) (color : ArcColoring V)
    (hA2 : NoInfinitePath (asymPart D color 0)) :
    ∃ v : V, InFam D color ({v} : Set V) := by sorry

end SandsSauerWoodrow
