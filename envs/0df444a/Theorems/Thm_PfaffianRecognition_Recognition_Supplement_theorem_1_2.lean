-- Prove2me | Theorems.Thm_PfaffianRecognition_Recognition_Supplement_theorem_1_2
-- name    : PfaffianRecognition.Recognition.Supplement.theorem_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:02:05.657416+00:00
-- url     : https://prove2.me/theorems/ece67fa7-3481-4388-914a-6269e560e018
-- title:
--   Theorem 1.2 — non-Pfaffian iff some cut reversal is strongly connected
-- statement:
--   Let $G$ be a matching covered graph (connected, with at least one edge, every edge in a perfect matching) and let $D$ be an orientation of $G$. For $X\subseteq V(G)$ let $D^X$ be $D$ with every edge of the cut $\partial(X)$ reversed. Then
--   $$
--   D\text{ is non-Pfaffian}\iff\exists X\subseteq V(G):\ D^X\text{ is strongly connected},
--   $$
--   where $D$ is Pfaffian when all perfect matchings of $G$ have the same sign under $D$, and strongly connected means every vertex can be reached from every other by a directed path.
--
--   This structural characterization holds for every matching covered graph, bipartite or not; with the randomized Pfaffian-orientation test it yields a randomized algorithm for making a matching covered graph strongly connected by reversing a cut, a problem that is NP-complete for general digraphs.
--
--   Differences from the source:
--   - encoding: arbitrary finite simple graph G → SimpleGraph (Fin N) for every N, vertices in a fixed order; reason: every finite simple graph has such a labelling; no instance is removed
--   - reading: matching covered (used, not defined, in the paper) → IsMatchingCovered: connected, at least one edge, every edge in some perfect matching; reason: the standard definition of [LP86]/[LM24] the paper cites; connectivity and an edge are part of it, and without them the statement fails on K1
-- source:
--   Priyanshu Pant, Ranveer Singh, Pfaffian Recognition is in coRP, STOC 2027 submission #858 (October 2026), Theorem 1.2, p. 4 (proof pp. 12–14); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/858.pdf

import Definitions.Def_PfaffianRecognition_Recognition_Supplement_cut_model

namespace PfaffianRecognition.Recognition.Supplement

open PfaffianRecognition.Recognition

/-- Theorem 1.2, p. 4 (proof pp. 12–14). For a matching covered graph `G` and an orientation `D`,
`D` is non-Pfaffian iff some cut reversal `D^X` is strongly connected. -/
theorem theorem_1_2 {N : ℕ} (G : SimpleGraph (Fin N)) (hG : IsMatchingCovered G)
    (D : Orientation G) :
    ¬ IsPfaffianOrientation D ↔
      ∃ X : Set (Fin N), IsStronglyConnected (cutReversal D X) := by sorry

end PfaffianRecognition.Recognition.Supplement
