-- Prove2me | Theorems.Thm_TuranMatching_Clique_case_analysis
-- name    : TuranMatching.Clique.case_analysis
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:29:44.66809+00:00
-- url     : https://prove2.me/theorems/512205ac-3449-4913-8934-dace3bed5d06
-- title:
--   §2, p. 4, Cases 1–4 — the structure left by Lemma 2.2 has at most $\max\{t(2s+1,k),g(n,k,s)\}$ edges
-- statement:
--   Let $k\ge2$, $n\ge2s+1$, and let $G$ be a graph on $n$ vertices with no clique on $k+1$ vertices. Let $B$ and $A$ be disjoint vertex sets with $b=|B|\le s$ and $|A|=2s-2b+1$, such that every vertex outside $B\cup A$ has all its neighbours in $B$ (the components of $G-B$ other than $A_1=A$ are isolated vertices). Then
--   $$|E(G)|\ \le\ \max\{t(2s+1,k),\ g(n,k,s)\}.$$
--
--   This is the case analysis on $b$ that ends the proof of Theorem 1.1 (Case 1: $b=0$; Case 2: $b=s$; Case 3: $2s-b+1\le s+\lfloor s/(k-1)\rfloor$; Case 4: $2s-b+1>s+\lfloor s/(k-1)\rfloor$).
--
--   **Formalization Note** No matching hypothesis is needed: the cases only count edges. The subtraction $2s-2b$ is in ℕ and is exact because $b\le s$. The paper says "every $k$"; the restriction $k\ge2$ is needed because $G(n,k,s)$ has $k-1$ classes of total size $s$, which is impossible for $k=1$ and $s>0$, and no graph on $n\ge1$ vertices has clique number at most $0$.
-- source:
--   Alon and Frankl, Turán graphs with bounded matching number, arXiv:2210.15076v1, p. 3, last sentence ("a_1 = 2s − 2b + 1"); p. 4, Cases 1–4

import Mathlib
import Definitions.Def_TuranMatching_Clique_Setting

open Finset SimpleGraph

namespace TuranMatching.Clique

theorem case_analysis (n k s : ℕ) (hk : 2 ≤ k) (hn : 2 * s + 1 ≤ n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hK : G.CliqueFree (k + 1))
    (B A : Finset (Fin n)) (hBA : Disjoint B A) (hb : #B ≤ s) (hA : #A = 2 * s - 2 * #B + 1)
    (hout : ∀ v, v ∉ B → v ∉ A → ∀ w, G.Adj v w → w ∈ B) :
    #G.edgeFinset ≤ max (turanNum (2 * s + 1) k) (gNum n k s) := by sorry

end TuranMatching.Clique
