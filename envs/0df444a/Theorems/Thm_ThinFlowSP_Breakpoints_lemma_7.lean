-- Prove2me | Theorems.Thm_ThinFlowSP_Breakpoints_lemma_7
-- name    : ThinFlowSP.Breakpoints.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:29:27.998203+00:00
-- url     : https://prove2.me/theorems/4d176576-8c30-433a-8b35-875f0054d00e
-- title:
--   Lemma 7, p. 7 — the normalization π is extensive and 1-Lipschitz in the sup norm
-- statement:
--   Let $G' = (V, A', A^*)$ be a shortest path graph with resetting and let $\pi : \mathbb R^V \to \mathbb R^V$ be the normalization function: along a topological order, $\pi_w(\ell') = \max\{\ell'_w, \min_{v\in N^-(w)}\pi_v(\ell')\}$ if $w \ne s$ and $\delta^-(w)\cap A^* = \emptyset$, and $\pi_w(\ell') = \ell'_w$ otherwise. Then
--
--   1. $\ell' \le \pi(\ell')$ for all $\ell' \in \mathbb R^V_{\ge 0}$, and
--   2. for all $\ell', \ell'' \in \mathbb R^V_{\ge 0}$,
--   $$\|\pi(\ell'') - \pi(\ell')\|_\infty \le \|\ell'' - \ell'\|_\infty .$$
--
--   The normalization repairs solutions of (LCP) into normalized thin flows (Corollary 8); its Lipschitz property transfers the local Lipschitz continuity of LCP solutions to the label function (Proposition 17).
--
--   **Formalization Note** $\|\cdot\|_\infty$ is the sup norm of `V → ℝ`. $\pi$ is computed by $|V|$ sweeps of the update, which agrees with the topological-order recursion on an acyclic graph.
-- source:
--   Kaiser, Computation of Dynamic Equilibria in Series-Parallel Networks, arXiv:2002.11428v2, p. 7, Lemma 7 (and the definition of π above it)

import Mathlib
import Definitions.Def_ThinFlowSP_Breakpoints_Model

namespace ThinFlowSP.Breakpoints

theorem lemma_7 (G : Net) (Astar : Finset G.A) (hG : IsShortestPathGraph G) :
    (∀ l : G.V → ℝ, (∀ v, 0 ≤ l v) → ∀ v, l v ≤ normalize G Astar l v) ∧
    (∀ l l' : G.V → ℝ, (∀ v, 0 ≤ l v) → (∀ v, 0 ≤ l' v) →
      ‖normalize G Astar l' - normalize G Astar l‖ ≤ ‖l' - l‖) := by sorry

end ThinFlowSP.Breakpoints
