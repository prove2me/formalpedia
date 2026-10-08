-- Prove2me | Theorems.Thm_TwinWidthI_FOInterp_lemma_5_2_graph
-- name    : TwinWidthI.FOInterp.lemma_5_2_graph
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:45:15.355298+00:00
-- url     : https://prove2.me/theorems/0aafe0f9-cdbb-4d60-8b65-e0a00429bd51
-- title:
--   Lemma 5.2 (graph form, as applied on p. 3:43) — a sequence of r-refining h-partitions gives twin-width at most r(h+1)
-- statement:
--   Let $G$ be a finite simple graph on $V$, and let $r,h\ge 0$ be integers. Suppose $\mathcal Q_0,\mathcal Q_1,\dots,\mathcal Q_s$ is a sequence of partitions of $V$ such that
--   1. $\mathcal Q_0$ is the partition into singletons (the finest partition);
--   2. $\mathcal Q_s$ has at most one part (the coarsest partition);
--   3. $\mathcal Q_i$ $r$-refines $\mathcal Q_{i+1}$ for every $i<s$;
--   4. every $\mathcal Q_i$ is an $h$-partition of $G$.
--
--   Then
--   $$\operatorname{tww}(G)\le r(h+1).$$
--
--   This is the graph form of Lemma 5.2: the sequence is completed into a contraction sequence by performing, in any order, the merges that lead from $\mathcal Q_i$ to $\mathcal Q_{i+1}$. It is the last step of the proof of Theorem 8.3, applied to the partitions $I_{\ell+2}(G,\mathcal P_i)$ of the interpretation $\varphi(G)$.
--
--   **Formalization Note.** Lemma 5.2 is printed for matrices, with row and column partitions of error value at most $t$, and conclusion $rt$. For a graph, read as a symmetric matrix, the error value of a part is its red degree plus its own diagonal zone, so $t=h+1$ and the bound $rt$ becomes $r(h+1)$; the application on p. 3:43 only needs some bound in terms of $r$ and $h$. "Coarsest partition" is "at most one part", which covers the empty graph.
-- source:
--   Bonnet, Kim, Thomassé and Watrigant, Twin-width I: Tractable FO Model Checking, J. ACM 69(1), Article 3 (2021), p. 3:18, Lemma 5.2 (matrix form), applied to graphs at the end of the proof of Theorem 8.3, p. 3:43

import Mathlib
import Definitions.Def_TwinWidthI_FOInterp_Setting

namespace TwinWidthI.FOInterp

open Finset

theorem lemma_5_2_graph {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (r h s : ℕ) (Q : Fin (s + 1) → Finpartition (univ : Finset V)) (h0 : Q 0 = ⊥)
    (hlast : #(Q (Fin.last s)).parts ≤ 1)
    (href : ∀ i : Fin s, RRefines r (Q i.castSucc) (Q i.succ))
    (hd : ∀ i, TwinWidthI.BoolWidth.IsDPartition G (Q i) h) :
    TwinWidthI.BoolWidth.TwinWidthLE G (r * (h + 1)) := by sorry

end TwinWidthI.FOInterp
