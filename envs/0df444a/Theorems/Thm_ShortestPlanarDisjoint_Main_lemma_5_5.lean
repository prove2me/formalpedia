-- Prove2me | Theorems.Thm_ShortestPlanarDisjoint_Main_lemma_5_5
-- name    : ShortestPlanarDisjoint.Main.lemma_5_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:38:41.103202+00:00
-- url     : https://prove2.me/theorems/f9b212be-2860-4e32-b0c8-e5cb479dd987
-- title:
--   Lemma 5.5 — Port expansion
-- statement:
--   For each graph configuration C, summing the actual weights of all port matchings projecting to C gives z^{ell(C)} p_C. Consequently the sign-free Pfaffian is the sum of z^{ell(C)} p_C over every configuration of the graph. Multiplicity-two edges contribute twice their cost and signature factor one. Paths and simple cycles use their full ordered transports. The empty Pfaffian and empty configuration contribute one.
--
--   Differences from the source:
--   - generalization: positive costs and crossing words of a planar embedding → all natural costs, every finite simple graph and arbitrary canonical edge crossing words; reason: the local expansion uses only the determinant-one crossing matrices and port incidences; zero costs and nonplanar ambient graphs do not alter either identity, and every source instance is included
--   - encoding: unoriented paths, cycles, doubled edges and projected port matchings → Fin n vertices, edge multiplicities zero, one or two with the exact degree constraints, canonical component traversals and enumerated Fin port indices; reason: these are bijective representations of source configurations and unordered matchings; costs and contributions are unchanged
-- source:
--   Srijan Chakraborty, Anish Mukherjee, STOC 2027 submission #1387 (October 2026), Lemma 5.5, p. 21 (PDF p. 23)

import Definitions.Def_ShortestPlanarDisjoint_Main_Configuration
set_option autoImplicit false

namespace ShortestPlanarDisjoint.Main
open scoped BigOperators
/-- Both the configuration-wise weight identity and the complete Pfaffian
expansion, with doubled edges counted twice in the actual cost. -/
theorem lemma_5_5 {n k r : ℕ} (I : RoutingInput n k) (words : EdgeWords n r)
    (ell : Sym2 (Fin n) → ℕ) :
    (∀ C : GraphConfiguration I,
      (∑ p : IndexMatching (Fintype.card (GraphPort I)),
        if projectsTo p C then portMatchingWeight I words ell p else 0) =
        Polynomial.monomial (C.cost ell) (C.signature words)) ∧
    matchingPfaffian (portMatrix I words ell) =
      ∑ C : GraphConfiguration I,
        Polynomial.monomial (C.cost ell) (C.signature words) := by sorry
end ShortestPlanarDisjoint.Main
