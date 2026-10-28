-- Prove2me | Theorems.Thm_ThinFlowSP_Breakpoints_lemma_11
-- name    : ThinFlowSP.Breakpoints.lemma_11
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T02:28:49.486407+00:00
-- url     : https://prove2.me/theorems/5430e714-a34d-443e-9daf-04dc80e51ef9
-- title:
--   Lemma 11, p. 8 — the weighted Laplacian factors as L = B D (B⁺)ᵀ
-- statement:
--   Let $G = (V, A')$ be a directed multigraph without self-loops, with arc weights $\nu \in \mathbb R^{A'}_{>0}$, incidence matrix $B$ (Definition 5) with positive part $B^+$, and weighted Laplacian $L$ (Definition 10). With $D = \mathrm{diag}(\nu)$,
--   $$L = B\,D\,(B^+)^\top .$$
--
--   The identity links the principal minors of the LCP matrix $M$ to those of Laplacians, which is how Lemma 9 is proved.
--
--   **Formalization Note** The page says "directed graph"; for a self-loop the incidence column is zero while the loop's weight enters $L_{v,v}$, so the identity needs the absence of self-loops, which is added as a hypothesis (every graph of the paper is acyclic). $\nu_{v,w}$ is read as the total weight of the arcs from $v$ to $w$.
-- source:
--   Kaiser, Computation of Dynamic Equilibria in Series-Parallel Networks, arXiv:2002.11428v2, p. 8, Lemma 11 (with Definition 10)

import Mathlib
import Definitions.Def_ThinFlowSP_Breakpoints_Network

namespace ThinFlowSP.Breakpoints

theorem lemma_11 (G : Net) (hloop : ∀ a, G.tail a ≠ G.head a) (ν : G.A → ℝ)
    (hν : ∀ a, 0 < ν a) :
    laplacian G ν = incidence G * Matrix.diagonal ν * (incPos G).transpose := by sorry

end ThinFlowSP.Breakpoints
