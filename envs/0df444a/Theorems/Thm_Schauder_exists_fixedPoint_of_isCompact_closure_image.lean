-- Prove2me | Theorems.Thm_Schauder_exists_fixedPoint_of_isCompact_closure_image
-- name    : Schauder.exists_fixedPoint_of_isCompact_closure_image
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-04T17:55:58.006203+00:00
-- url     : https://prove2.me/theorems/44209415-7356-43bd-9ba4-bee8c6f1f1fd
-- title:
--   Schauder fixed point theorem: a continuous self-map of a closed convex set with precompact image has a fixed point
-- statement:
--   **Schauder fixed point theorem.** Let $E$ be a real Banach space, let $G\subseteq E$ be a nonempty, closed, convex set, and let $T: E\to E$ be continuous on $G$ with $T(G)\subseteq G$. If the image $T(G)$ is precompact, i.e. its closure $\overline{T(G)}$ is compact, then $T$ has a fixed point in $G$:
--   $$\exists\,x\in G,\qquad T x = x .$$
--
--   This is the form of Schauder's theorem invoked in the proof of Theorem 3.15 of Carmona–Cooney–Graves–Laurière (applied with $G=L^2(I)$ to the operator $\mathbf B\mathbf Z$, whose range lies in a compact set). The nonemptiness of $G$ is implicit in the textbook statement and is required (the empty set is closed and convex). The standard proof approximates $T$ by finite-dimensional maps via Schauder projections onto finite $\varepsilon$-nets of $\overline{T(G)}$ and applies Brouwer's fixed point theorem (available on the platform as `AGT.brouwer_fixed_point`), then passes to the limit using compactness.
-- source:
--   Gilbarg & Trudinger, Elliptic Partial Differential Equations of Second Order (Springer, 2001 reprint), Section 11.1, Corollary 11.2 (Schauder fixed point theorem); used in Carmona, Cooney, Graves & Laurière, Stochastic Graphon Games: I. The Static Case, arXiv:1911.10664v1, p. 15, proof of Theorem 3.15

import Mathlib

namespace Schauder

theorem exists_fixedPoint_of_isCompact_closure_image {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {G : Set E} (hGc : IsClosed G) (hGconv : Convex ℝ G)
    (hGne : G.Nonempty) (T : E → E) (hT : ContinuousOn T G) (hTG : Set.MapsTo T G G)
    (hpre : IsCompact (closure (T '' G))) : ∃ x ∈ G, T x = x := by sorry

end Schauder
