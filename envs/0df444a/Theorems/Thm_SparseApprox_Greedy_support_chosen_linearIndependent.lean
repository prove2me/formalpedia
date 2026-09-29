-- Prove2me | Theorems.Thm_SparseApprox_Greedy_support_chosen_linearIndependent
-- name    : SparseApprox.Greedy.support_chosen_linearIndependent
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:23:37.28205+00:00
-- url     : https://prove2.me/theorems/9400e648-191f-46d5-ab81-25bcfd9f2921
-- title:
--   Proof of Lemma 2, p. 232 — $\sigma(A^{(0)})\cup\tau(A^{(0)})$ is linearly independent
-- statement:
--   Throughout, $A\in\mathbb R^{m\times n}$, $b\in\mathbb R^m$ and $\varepsilon>0$ are the input of Algorithm Greedy, and $k_0,k_1,\dots$ are the indices it selects. For $r<t$, $A^{(r)}$ (columns $a^{(r)}_j$), $b^{(r)}$ and $\tau^{(r)}$ are the columns, the vector $b$ and the set of chosen indices at the start of iteration $r$ of a run of $t$ selection iterations, as computed by the algorithm.
--
--   Let $r<t$ and let $u^{(r)}$ be a vector with the minimum number of nonzero entries such that $\|A^{(r)}u^{(r)}-b^{(r)}\|_2\le\varepsilon/2$. Let $\sigma=\{i : u^{(r)}_i\neq 0\}$ and let $\tau=\{k_0,\dots,k_{r-1}\}$ be the indices of the first $r$ columns picked by the algorithm. Then
--   1. $\sigma$ and $\tau$ are disjoint, and
--   2. the columns $\{a^{(0)}_i : i\in\sigma\cup\tau\}$ of $A^{(0)}=\mathbf A$ are linearly independent.
--
--   This is the structural fact behind Lemma 2: it makes the matrix $Z$ with these columns have a left inverse, which lets $u^{(r)}$ be recovered from $A^{(r)}u^{(r)}$ through the pseudo-inverse $Z^+$.
--
--   **Formalization Note** Disjointness is implicit on the page (the proof of Lemma 2 sets $u^{(r)}_i=0$ for $i\in\tau$) and is stated explicitly. Linear independence is stated for the family indexed by $\sigma\cup\tau$, so it also excludes repeated columns.
-- source:
--   Natarajan, Sparse Approximate Solutions to Linear Systems, SIAM J. Comput. 24 (1995), p. 232, proof of Lemma 2, second paragraph ("We first show that σ(A⁽⁰⁾) ⋃ τ(A⁽⁰⁾) is a linearly independent set")

import Mathlib
import Definitions.Def_SparseApprox_Greedy_Basic
import Definitions.Def_SparseApprox_Greedy_Algorithm

open scoped InnerProductSpace

namespace SparseApprox.Greedy

theorem support_chosen_linearIndependent {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : EuclideanSpace ℝ (Fin m)) (ε : ℝ) (hε : 0 < ε) (k : ℕ → Fin n) (t : ℕ)
    (hrun : IsGreedyRun A b ε k t) (r : ℕ) (hr : r < t) (u : EuclideanSpace ℝ (Fin n))
    (hu : IsMinSparseSol (greedyState A b k r).col (greedyState A b k r).res (ε / 2) u) :
    Disjoint (nzSet u) (greedyState A b k r).chosen ∧
      LinearIndependent ℝ
        (fun i : ↥(nzSet u ∪ (greedyState A b k r).chosen) => (initState A b).col i) := by sorry

end SparseApprox.Greedy
