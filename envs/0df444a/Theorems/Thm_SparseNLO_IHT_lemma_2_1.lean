-- Prove2me | Theorems.Thm_SparseNLO_IHT_lemma_2_1
-- name    : SparseNLO.IHT.lemma_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T16:08:30.224594+00:00
-- url     : https://prove2.me/theorems/720d9f2b-42d0-4733-903e-95174f2da8c0
-- title:
--   Lemma 2.1 — for f_LI(x) = ‖Ax − b‖² with A s-regular, problem (P) has finitely many BF points
-- statement:
--   Let $0<s<n$, let $A\in\mathbb R^{m\times n}$ be an $s$-regular matrix (every $s$ of its columns are linearly independent) and let $b\in\mathbb R^m$. Take $f=f_{LI}$,
--   $$f_{LI}(x)=\|Ax-b\|^2 .$$
--   Then the set of basic feasible (BF) points of problem (P),
--   $$\{x\in C_s:\ \|x\|_0<s\Rightarrow\nabla f_{LI}(x)=0,\ \ \|x\|_0=s\Rightarrow\nabla_i f_{LI}(x)=0\ \forall i\in I_1(x)\},$$
--   is finite.
--
--   Finiteness of the BF points is what lets the proof of Theorem 3.2 separate the candidate limits of the IHT method by a positive distance.
--
--   **Formalization Note** $Ax$ is `Matrix.toEuclideanLin A x` and $\|\cdot\|$ is the Euclidean norm on `EuclideanSpace ℝ (Fin m)`. Assumption 1 holds automatically for $f_{LI}\ge0$ and is not stated.
-- source:
--   Beck, Eldar, Sparsity Constrained Nonlinear Optimization: Optimality Conditions and Algorithms, SIAM J. Optim. (2013), doi:10.1137/120869778 (source: arXiv:1203.4580v1), p. 6, Lemma 2.1

import Mathlib
import Definitions.Def_SparseNLO_IHT_Setting

open Filter Topology

namespace SparseNLO.IHT

/-- Lemma 2.1 (p. 6). Let `f = f_LI`, `f_LI(x) = ‖Ax − b‖²`, where `A ∈ ℝ^{m×n}` is `s`-regular and
`b ∈ ℝ^m`. Then the number of BF points of problem (P) is finite. -/
theorem lemma_2_1 {m n s : ℕ} (hs : 0 < s) (hsn : s < n)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin m)) (hA : IsSRegular s A) :
    {x : EuclideanSpace ℝ (Fin n) | SparseNLO.CWOpt.IsBF (fLI A b) s x}.Finite := by sorry

end SparseNLO.IHT
