-- Prove2me | Theorems.Thm_TwinWidthI_MinorFree_theorem_5_8
-- name    : TwinWidthI.MinorFree.theorem_5_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T08:39:42.813991+00:00
-- url     : https://prove2.me/theorems/d850aed3-9ef7-4bbc-bd91-e4a8958fa66e
-- title:
--   Theorem 5.8 (graphs, explicit constant of p. 3:29) — a k-mixed-free adjacency order gives twin-width ≤ 4c_k·2^(4c_k+2)
-- statement:
--   Let $G$ be a finite graph and let $\sigma$ order its vertices. If $k\ge1$ and its Boolean adjacency matrix $A_\sigma(G)$ is $k$-mixed free, then
--
--   $$
--   \operatorname{tww}(G)\le
--   \left\lfloor 4c_k2^{4c_k+2}\right\rfloor,
--   \qquad c_k=\frac83(k+1)^2 2^{4k}.
--   $$
--
--   This is the symmetric graph version of the matrix grid theorem and converts a matrix order into a graph contraction sequence.
--
--   **Formalization Note** Theorem 5.8 prints an asymptotic bound; the explicit constant is the one applied to graphs at the end of Theorem 6.3 on p. 3:29. The threshold $k\ge1$ states the nondegenerate division range.
-- source:
--   Bonnet, Kim, Thomassé and Watrigant, Twin-width I: Tractable FO Model Checking, J. ACM 69(1), Article 3 (2021), pp. 3:22–3:23, Theorem 5.8 and proof; p. 3:29, proof of Theorem 6.3, explicit bound

import Mathlib
import Definitions.Def_TwinWidthI_MinorFree_Setting

namespace TwinWidthI.MinorFree

/-- The graph specialization of Theorem 5.8, with the explicit constant used on p. 3:29. -/
theorem theorem_5_8 {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {n : ℕ} (σ : V ≃ Fin n) (k : ℕ) (hk : 1 ≤ k)
    (hM : TwinWidthI.GridThm.MixedFree (adjMat G σ) k) :
    TwinWidthI.BoolWidth.TwinWidthLE G ⌊4 * TwinWidthI.GridThm.cMT k * (2 : ℝ) ^ (4 * TwinWidthI.GridThm.cMT k + 2)⌋₊ := by sorry

end TwinWidthI.MinorFree
