-- Prove2me | Theorems.Thm_PfaffianRecognition_Recognition_Supplement_lemma_4_3
-- name    : PfaffianRecognition.Recognition.Supplement.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:01:27.188321+00:00
-- url     : https://prove2.me/theorems/84cf7604-fdb3-4610-9ea0-93b48278f743
-- title:
--   Lemma 4.3 — reversing a cut preserves Pfaffianity
-- statement:
--   Let $G$ be a finite simple graph with a perfect matching, $D$ an orientation of $G$ and $X\subseteq V(G)$. Let $D^X$ be obtained from $D$ by reversing every edge with exactly one endpoint in $X$. Then
--   $$
--   D\text{ is Pfaffian}\iff D^X\text{ is Pfaffian}.
--   $$
--   The paper attributes this to [dCLM05]; it is used in the converse direction of Theorem 1.2.
--
--   Differences from the source:
--   - encoding: arbitrary finite simple graph G → SimpleGraph (Fin N) for every N, vertices in a fixed order; reason: every finite simple graph has such a labelling; no instance is removed
-- source:
--   Priyanshu Pant, Ranveer Singh, Pfaffian Recognition is in coRP, STOC 2027 submission #858 (October 2026), Lemma 4.3, p. 12; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/858.pdf

import Definitions.Def_PfaffianRecognition_Recognition_Supplement_cut_model

namespace PfaffianRecognition.Recognition.Supplement

open PfaffianRecognition.Recognition

/-- Lemma 4.3, p. 12 ([dCLM05]). Reversing the edges of a cut preserves Pfaffianity. -/
theorem lemma_4_3 {N : ℕ} {G : SimpleGraph (Fin N)}
    (hG : ∃ F : Finset G.edgeSet, MulmuleyVV.Matching.IsPerfectMatchingEdges G F)
    (D : Orientation G) (X : Set (Fin N)) :
    IsPfaffianOrientation D ↔ IsPfaffianOrientation (cutReversal D X) := by sorry

end PfaffianRecognition.Recognition.Supplement
