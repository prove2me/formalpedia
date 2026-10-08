-- Prove2me | Theorems.Thm_TwinWidthI_BoolWidth_twinWidth_le_of_card_le
-- name    : TwinWidthI.BoolWidth.twinWidth_le_of_card_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:31:48.303762+00:00
-- url     : https://prove2.me/theorems/c6b0ac69-34c5-48cf-a875-bad621755aa4
-- title:
--   Proof of Theorem 4.2, p. 3:14 — a graph with at most N vertices has twin-width at most N
-- statement:
--   Let $G$ be a finite simple graph with vertex set $V$ and let $N\ge 0$ be an integer. If $G$ has at most $N$ vertices, then
--   $$\operatorname{tww}(G)\le N .$$
--
--   In the proof of Theorem 4.2 (with $N=2^k$) this disposes of graphs with at most $2^k$ vertices, so that the remaining argument may assume $|V|\ge 2^k+1$.
--
--   **Formalization Note.** $\operatorname{tww}(G)\le N$ is the predicate `TwinWidthLE G N` of the setting (sequences of $N$-partitions from singletons to at most one part). No lower bound on $N$ or $|V|$ is assumed; the empty graph is covered.
-- source:
--   Bonnet, Kim, Thomassé and Watrigant, Twin-width I: Tractable FO Model Checking, J. ACM 69(1), Article 3 (2021), p. 3:14, proof of Theorem 4.2, "otherwise the twin-width is immediately bounded by 2^k"

import Mathlib
import Definitions.Def_TwinWidthI_BoolWidth_Setting

namespace TwinWidthI.BoolWidth

open Finset

theorem twinWidth_le_of_card_le {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (N : ℕ) (hcard : Fintype.card V ≤ N) : TwinWidthLE G N := by sorry

end TwinWidthI.BoolWidth
