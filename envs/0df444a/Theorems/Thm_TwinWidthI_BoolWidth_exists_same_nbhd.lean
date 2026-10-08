-- Prove2me | Theorems.Thm_TwinWidthI_BoolWidth_exists_same_nbhd
-- name    : TwinWidthI.BoolWidth.exists_same_nbhd
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:30:38.340027+00:00
-- url     : https://prove2.me/theorems/f6d9c38f-4e03-4f98-a56e-0332058383b7
-- title:
--   Proof of Theorem 4.2, p. 3:14 — at most N neighbourhoods and N+1 vertices force two twins across the cut
-- statement:
--   Let $G$ be a finite simple graph on $V$, let $A,B\subseteq V$ be disjoint, and let $N\ge 0$. Suppose the number of different neighbourhoods in $B$ of subsets of $A$ is at most $N$,
--   $$\nu_G(A,B)=\bigl|\{N(S)\cap B: S\subseteq A\}\bigr|\le N,$$
--   and $|A|\ge N+1$. Then there are two distinct vertices $u\neq v$ in $A$ with the same neighbourhood in $B$: for every $b\in B$, $ub$ is an edge if and only if $vb$ is an edge.
--
--   In the proof of Theorem 4.2 this is applied to the cut $P_e=(A_e,B_e)$ of boolean-width at most $k$, with $N=2^k$ and $|A_e|\ge 2^k+1$; the two vertices $u, v$ are the first pair to be contracted.
--
--   **Formalization Note.** $\nu_G(A,B)$ is `nbhdCount G A B`, which counts neighbourhoods of all subsets of $A$, including the empty set.
-- source:
--   Bonnet, Kim, Thomassé and Watrigant, Twin-width I: Tractable FO Model Checking, J. ACM 69(1), Article 3 (2021), p. 3:14, proof of Theorem 4.2, "among the 2^k + 1 leaves of T′, corresponding to, say, A_e, two vertices u,v have the same neighborhood in B_e"

import Mathlib
import Definitions.Def_TwinWidthI_BoolWidth_Setting

namespace TwinWidthI.BoolWidth

open Finset

theorem exists_same_nbhd {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (A B : Finset V) (hAB : Disjoint A B) (N : ℕ)
    (hcount : nbhdCount G A B ≤ N) (hA : N + 1 ≤ #A) :
    ∃ u ∈ A, ∃ v ∈ A, u ≠ v ∧ ∀ b ∈ B, (G.Adj u b ↔ G.Adj v b) := by sorry

end TwinWidthI.BoolWidth
