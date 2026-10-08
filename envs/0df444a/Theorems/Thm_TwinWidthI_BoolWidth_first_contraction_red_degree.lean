-- Prove2me | Theorems.Thm_TwinWidthI_BoolWidth_first_contraction_red_degree
-- name    : TwinWidthI.BoolWidth.first_contraction_red_degree
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:30:46.654049+00:00
-- url     : https://prove2.me/theorems/9444af0c-9da8-4ebc-80f5-3c038302b3d5
-- title:
--   Proof of Theorem 4.2, p. 3:14 — contracting two twins across the cut gives a (2N − 1)-partition
-- statement:
--   Let $G$ be a finite simple graph on $V$, let $(A,B)$ be a partition of $V$ (that is, $A\cap B=\emptyset$ and $A\cup B=V$), and let $N\ge 0$ with $|A|\le 2N$. Let $u\neq v$ be two vertices of $A$ with the same neighbourhood in $B$. Let $\mathcal P$ be the partition of $V$ whose parts are $\{u,v\}$ and the singletons $\{w\}$, $w\notin\{u,v\}$ (the partition after contracting $u$ and $v$). Then $\mathcal P$ is a $(2N-1)$-partition: every part of $\mathcal P$ is non-homogeneous to at most
--   $$2N-1$$
--   other parts.
--
--   With $N=2^k$ this is the paper's claim that after the first contraction all red edges lie within $A_e$, so the red degree is at most $2^{k+1}-1$.
--
--   **Formalization Note.** The contracted graph $G/u,v$ is represented by the partition $\mathcal P$ (partition form of twin-width); the hypothesis `hP` fixes its parts. The subtraction $2N-1$ is in $\mathbb N$; it is exact whenever the hypotheses hold, since $u\in A$ forces $N\ge 1$.
-- source:
--   Bonnet, Kim, Thomassé and Watrigant, Twin-width I: Tractable FO Model Checking, J. ACM 69(1), Article 3 (2021), p. 3:14, proof of Theorem 4.2, "The only red edges in G/u,v are within A_e, so the red degree is bounded by 2^{k+1} − 1"

import Mathlib
import Definitions.Def_TwinWidthI_BoolWidth_Setting

namespace TwinWidthI.BoolWidth

open Finset

theorem first_contraction_red_degree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A B : Finset V) (hAB : Disjoint A B) (hcover : A ∪ B = univ)
    (N : ℕ) (hA : #A ≤ 2 * N) (u v : V) (hu : u ∈ A) (hv : v ∈ A) (huv : u ≠ v)
    (htwin : ∀ b ∈ B, (G.Adj u b ↔ G.Adj v b))
    (P : Finpartition (univ : Finset V))
    (hP : P.parts = insert {u, v} (((univ.erase u).erase v).image fun w => ({w} : Finset V))) :
    IsDPartition G P (2 * N - 1) := by sorry

end TwinWidthI.BoolWidth
