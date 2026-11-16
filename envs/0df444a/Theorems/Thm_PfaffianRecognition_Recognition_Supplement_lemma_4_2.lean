-- Prove2me | Theorems.Thm_PfaffianRecognition_Recognition_Supplement_lemma_4_2
-- name    : PfaffianRecognition.Recognition.Supplement.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:00:51.945549+00:00
-- url     : https://prove2.me/theorems/46189b94-daea-4951-8ca3-7a7331989b34
-- title:
--   Lemma 4.2 — ear decompositions extend from a conformal matching covered subgraph
-- statement:
--   Let $G$ be a matching covered graph and let $H$ be a conformal matching covered subgraph of $G$ (so $G-V(H)$ has a perfect matching). Then there are $t\ge0$ and subgraphs
--   $$
--   H=H_0\subseteq H_1\subseteq\cdots\subseteq H_t=G,
--   $$
--   each of them matching covered, such that every $H_{i+1}$ is obtained from $H_i$ by adding either one odd ear of $H_i$ or two vertex-disjoint odd ears of $H_i$. An odd ear of $H_i$ is a path of odd length with both endpoints in $V(H_i)$, internal vertices outside $V(H_i)$ and no edge of $H_i$.
--
--   This is the ear-decomposition theorem of Lovász and Plummer in the form [LM24, Theorem 11.11]; it drives the induction in the forward direction of Theorem 1.2.
--
--   **Formalization Note** The chain is indexed by `Fin (t+1)`; $H_t=G$ is the top subgraph; inclusion follows from each step being a supremum with the added ears.
--
--   Differences from the source:
--   - encoding: arbitrary finite simple graph G → SimpleGraph (Fin N) for every N, vertices in a fixed order; reason: every finite simple graph has such a labelling; no instance is removed
--   - reading: matching covered (used, not defined, in the paper) → IsMatchingCovered: connected, at least one edge, every edge in some perfect matching; reason: the standard definition of [LP86]/[LM24] the paper cites; connectivity and an edge are part of it, and without them the statement fails on K1
--   - reading: two vertex disjoint odd ears → two odd ears of H_i with no common vertex, endpoints included; reason: the literal reading and the two-ear theorem of Lovász–Plummer; it is the stronger existence claim
-- source:
--   Priyanshu Pant, Ranveer Singh, Pfaffian Recognition is in coRP, STOC 2027 submission #858 (October 2026), Lemma 4.2, p. 12; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/858.pdf

import Definitions.Def_PfaffianRecognition_Recognition_Supplement_cut_model

namespace PfaffianRecognition.Recognition.Supplement

open PfaffianRecognition.Recognition

/-- Lemma 4.2, p. 12 ([LM24, Theorem 11.11]). An ear decomposition of a matching covered graph
extends from any conformal matching covered subgraph `H`: matching covered subgraphs
`H = H₀ ⊆ ⋯ ⊆ H_t = G`, each obtained from the previous one by adding one odd ear or two vertex
disjoint odd ears. -/
theorem lemma_4_2 {N : ℕ} {G : SimpleGraph (Fin N)} (hG : IsMatchingCovered G)
    (H : G.Subgraph) (hH : IsMatchingCoveredSubgraph H) (hconf : IsConformalSet G H.verts) :
    ∃ (t : ℕ) (Hs : Fin (t + 1) → G.Subgraph),
      Hs 0 = H ∧ Hs (Fin.last t) = ⊤ ∧ (∀ i, IsMatchingCoveredSubgraph (Hs i)) ∧
        ∀ i : Fin t, IsEarStep (Hs i.castSucc) (Hs i.succ) := by sorry

end PfaffianRecognition.Recognition.Supplement
