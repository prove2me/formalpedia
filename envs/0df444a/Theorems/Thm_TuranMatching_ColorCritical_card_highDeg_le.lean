-- Prove2me | Theorems.Thm_TuranMatching_ColorCritical_card_highDeg_le
-- name    : TuranMatching.ColorCritical.card_highDeg_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:33:34.381993+00:00
-- url     : https://prove2.me/theorems/bb4cd4c0-7f3e-4b8e-9455-e36fe70a48d2
-- title:
--   Proof of Prop. 3.1, p. 5 — a graph with matching number ≤ s has at most s vertices of degree exceeding 2s
-- statement:
--   Let $G$ be a graph on $n$ vertices with matching number $\nu(G)\le s$, and let $X$ be the set of vertices of $G$ of degree exceeding $2s$. Then
--   $$|X|\le s.$$
--
--   This is the first step of the proof of Proposition 3.1: it isolates a small set of high-degree vertices, after which every remaining vertex has degree at most $2s$.
-- source:
--   Alon and Frankl, Turán graphs with bounded matching number, arXiv:2210.15076v1, p. 5, proof of Proposition 3.1, second paragraph, first sentence

import Mathlib
import Definitions.Def_TuranMatching_ColorCritical_Setting

open Finset SimpleGraph

namespace TuranMatching.ColorCritical

theorem card_highDeg_le {n : ℕ} (s : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : TuranMatching.Clique.matchingNumber G ≤ s) : #(highDeg G s) ≤ s := by sorry

end TuranMatching.ColorCritical
