-- Prove2me | Theorems.Thm_PersistClust_Count_theorem_4_5_matching_assembly
-- name    : PersistClust.Count.theorem_4_5_matching_assembly
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-12T05:50:08.558902+00:00
-- url     : https://prove2.me/theorems/6465663a-6c3f-4401-829c-fd9910966123
-- title:
--   Theorem 4.5, assembly step: demand routings in both directions yield the multi-bijection (i)–(iv)
-- statement:
--   This is the assembly step of the proof of Theorem 4.5 of RR-6968: it converts injective demand routings between two persistence diagrams into the multi-bijection with the matching guarantees (i)–(iv).
--
--   Let $D_X$ and $D_Y$ be two persistence diagrams off the diagonal (every point of positive multiplicity has death strictly smaller than birth) with finite off-diagonal support. Fix a level $\alpha$ and a radius $\varepsilon \ge 0$. An off-diagonal copy of $D_X$ is *demanding* if it is prominent — its point lies strictly above $\alpha$ in both coordinates and cannot be $\varepsilon$-absorbed by the diagonal — or if it is a high far south-east copy: birth above $\alpha + \varepsilon$ and more than $2\varepsilon$ above the death coordinate.
--
--   Suppose that in each direction the demanding copies admit an injective routing: an injection from the demanding copies of $D_X$ into the copies of $D_Y$ that maps prominent copies to copies $\varepsilon$-close in both coordinates, and high far south-east copies to south-east copies $\varepsilon$-close in the birth coordinate whose points again lie in $Q^{SE}_\alpha$; and symmetrically an injection from the demanding copies of $D_Y$ into the copies of $D_X$. Then there exists a bijection $\gamma$ between all copies of $D_X$ and all copies of $D_Y$ — off-diagonal copies together with the countably many diagonal slots — such that:
--
--   1. every copy of a point of $Q^{NE}_\alpha$ is mapped to a copy $\varepsilon$-close in both coordinates, in both directions (assertions (i) and (ii));
--   2. every copy of a point of $Q^{SE}_\alpha$ is mapped to a copy $\varepsilon$-close in the birth coordinate, in both directions (assertions (iii) and (iv)).
--
--   The construction routes each demanding copy to its partner and absorbs every other off-diagonal copy into the diagonal: a killed copy lands on a diagonal slot $\varepsilon$-close in the relevant coordinates, diagonal copies land on even slots and killed copies on odd slots of a per-diagram copy code, so the two total maps are injections preserving the clause relation, and the Schröder–Bernstein theorem yields the bijection $\gamma$; the clause relation of the images is exactly what assertions (i)–(iv) state.
--
--   **Formalization Note** The diagrams are functions from the extended plane to $\mathbb{N} \cup \{\infty\}$; copies are the elements of the `Copies` type (off-diagonal copies plus diagonal slots); closeness is the extended-real `closeE` with $\pm\infty$ close only to itself. The hypotheses are exactly diagram-likeness, finite support, and the two routings; no filtration or module data enters, so the lemma applies to any pair of diagrams for which the routings can be produced.
-- source:
--   Chazal–Guibas–Oudot–Skraba, Persistence-Based Clustering in Riemannian Manifolds, INRIA RR-6968, 2009, pp. 18–21, the copy-routing and multi-bijection construction in the proof of Theorem 4.5; packaged as a standalone lemma with the demand predicates made explicit

import Mathlib
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_MatchingGate

import Mathlib
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_MatchingGate

namespace PersistClust.Count

theorem theorem_4_5_matching_assembly
    {DX DY : EReal × EReal → ℕ∞} (α ε : ℝ) (hε : 0 ≤ ε)
    (hDX : IsDiagramLike DX) (hDY : IsDiagramLike DY)
    (hFinX : {p : EReal × EReal | DX p ≠ 0}.Finite)
    (hFinY : {p : EReal × EReal | DY p ≠ 0}.Finite)
    (hGX : ∃ F : {a : offD DX // DemandsOff α ε a} → offD DY,
        Function.Injective F ∧
        (∀ a, PromQNE α ε a.1 → CloseCopy2 ε a.1 (F a)) ∧
        (∀ a, offPt a.1 ∈ QSE α → CloseCopy1 ε a.1 (F a) ∧ offPt (F a) ∈ QSE α))
    (hGY : ∃ F : {a : offD DY // DemandsOff α ε a} → offD DX,
        Function.Injective F ∧
        (∀ a, PromQNE α ε a.1 → CloseCopy2 ε a.1 (F a)) ∧
        (∀ a, offPt a.1 ∈ QSE α → CloseCopy1 ε a.1 (F a) ∧ offPt (F a) ∈ QSE α)) :
    ∃ γ : Copies DX ≃ Copies DY, SatisfiesIIV γ α ε := by sorry

end PersistClust.Count
