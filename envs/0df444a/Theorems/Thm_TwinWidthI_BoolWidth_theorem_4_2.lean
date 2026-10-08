-- Prove2me | Theorems.Thm_TwinWidthI_BoolWidth_theorem_4_2
-- name    : TwinWidthI.BoolWidth.theorem_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:30:45.954193+00:00
-- url     : https://prove2.me/theorems/ba1cd6bd-dce3-4e7e-805b-8f18929a16e0
-- title:
--   Theorem 4.2 — every graph with boolean-width k has twin-width at most 2^{k+1} − 1
-- statement:
--   **Theorem 4.2.** Every graph with boolean-width $k$ has twin-width at most $2^{k+1}-1$.
--
--   Precisely: let $G$ be a finite simple graph and $N\ge 0$ an integer such that $G$ has a decomposition tree $T$ in which every edge $e$ induces a cut $(A_e,B_e)$ with at most $N$ different neighbourhoods in $B_e$ of subsets of $A_e$. Then
--   $$\operatorname{tww}(G)\ \le\ 2N-1 .$$
--   For $N=2^k$, the least such count when $\operatorname{boolw}(G)=k$, this is $\operatorname{tww}(G)\le 2^{k+1}-1$.
--
--   Since $\operatorname{boolw}(G)\le\operatorname{modw}(G)\le\operatorname{cw}(G)\le 2^{\operatorname{rw}(G)+1}-1$, the theorem shows that classes of bounded boolean-width, clique-width or rank-width have bounded twin-width.
--
--   **Formalization Note.** Boolean-width is kept as the integer count $N=2^{\operatorname{boolw}(G)}$ (`BoolWidthLE G N`) rather than its base-2 logarithm, and twin-width as the predicate `TwinWidthLE G d`. Since $\operatorname{boolw}(G)=k$ means that the least $N$ with `BoolWidthLE G N` is $N=2^k$ (an integer, being a count, although $k$ itself need not be), and then $2^{k+1}-1=2N-1$, the statement is exactly Theorem 4.2; for larger $N$ it follows from the case of the least $N$ because `TwinWidthLE` is monotone in its bound. The subtraction $2N-1$ is in $\mathbb N$; for $N=0$ the hypothesis forces $|V|=1$ (a graph with two or more vertices has a cut with at least one neighbourhood), where twin-width $0$ is correct. A graph on the empty vertex set has no decomposition tree, so the statement says nothing about it.
-- source:
--   Bonnet, Kim, Thomassé and Watrigant, Twin-width I: Tractable FO Model Checking, J. ACM 69(1), Article 3 (2021), p. 3:14, Theorem 4.2

import Mathlib
import Definitions.Def_TwinWidthI_BoolWidth_Setting

namespace TwinWidthI.BoolWidth

open Finset

theorem theorem_4_2 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (N : ℕ) (hN : BoolWidthLE G N) : TwinWidthLE G (2 * N - 1) := by sorry

end TwinWidthI.BoolWidth
