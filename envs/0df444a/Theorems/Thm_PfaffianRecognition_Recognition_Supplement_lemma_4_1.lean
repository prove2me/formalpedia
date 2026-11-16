-- Prove2me | Theorems.Thm_PfaffianRecognition_Recognition_Supplement_lemma_4_1
-- name    : PfaffianRecognition.Recognition.Supplement.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:00:00.600711+00:00
-- url     : https://prove2.me/theorems/8b2afa8d-286e-4171-a0f7-04c2cf5dbbd8
-- title:
--   Lemma 4.1 — Pfaffian iff every conformal even cycle is oddly oriented
-- statement:
--   Let $G$ be a finite simple graph that has a perfect matching and let $D$ be an orientation of $G$. Call $D$ Pfaffian when all perfect matchings of $G$ have the same sign under $D$. A cycle $C$ of $G$ is conformal when $G-V(C)$ has a perfect matching, and oddly oriented when an odd number of its edges are directed along its direction of traversal. Then
--   $$
--   D\text{ is Pfaffian}\iff\text{every conformal even cycle of }G\text{ is oddly oriented in }D .
--   $$
--   This is the classical characterization of Lovász and Plummer [LP86, Theorem 8.3.2]; it starts the forward direction of the proof of Theorem 1.2.
--
--   **Formalization Note** A cycle is a closed Mathlib walk with `IsCycle`, quantified over every starting vertex and both directions; for an even cycle the parity of forward edges is the same for both directions.
--
--   Differences from the source:
--   - encoding: arbitrary finite simple graph G → SimpleGraph (Fin N) for every N, vertices in a fixed order; reason: every finite simple graph has such a labelling; no instance is removed
--   - encoding: cycle of G with a fixed direction of traversal → closed walk C : G.Walk u u with C.IsCycle, every start vertex and direction; reason: each cycle appears once per start and direction; oddness of the forward count is the same for all of them on an even cycle
-- source:
--   Priyanshu Pant, Ranveer Singh, Pfaffian Recognition is in coRP, STOC 2027 submission #858 (October 2026), Lemma 4.1, p. 12; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/858.pdf

import Definitions.Def_PfaffianRecognition_Recognition_Supplement_cut_model

namespace PfaffianRecognition.Recognition.Supplement

open PfaffianRecognition.Recognition

/-- Lemma 4.1, p. 12 ([LP86, Theorem 8.3.2]). For a graph with a perfect matching, an orientation
is Pfaffian iff every conformal even cycle is oddly oriented. -/
theorem lemma_4_1 {N : ℕ} {G : SimpleGraph (Fin N)}
    (hG : ∃ F : Finset G.edgeSet, MulmuleyVV.Matching.IsPerfectMatchingEdges G F)
    (D : Orientation G) :
    IsPfaffianOrientation D ↔
      ∀ (u : Fin N) (C : G.Walk u u), C.IsCycle → Even C.length →
        IsConformalSet G {v | v ∈ C.support} → IsOddlyOriented D C := by sorry

end PfaffianRecognition.Recognition.Supplement
