-- Prove2me | Theorems.Thm_PinningSync_Tree_lemma_2_13
-- name    : PinningSync.Tree.lemma_2_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:18:45.492994+00:00
-- url     : https://prove2.me/theorems/8f00c275-e57a-4a3e-96f1-14bee00567e2
-- title:
--   Lemma 2.13, p. 1401 — Schur complement: (Q S; Sᵀ R) > 0 iff Q > 0 and R − SᵀQ⁻¹S > 0, iff R > 0 and Q − SR⁻¹Sᵀ > 0
-- statement:
--   Let $\mathcal Q\in\mathbb R^{p\times p}$ and $\mathcal R\in\mathbb R^{q\times q}$ be symmetric and $\mathcal S\in\mathbb R^{p\times q}$. Then the following three conditions are equivalent:
--   $$
--   \begin{pmatrix}\mathcal Q&\mathcal S\\ \mathcal S^{\mathsf T}&\mathcal R\end{pmatrix}>0,
--   $$
--   1. $\mathcal Q>0$ and $\mathcal R-\mathcal S^{\mathsf T}\mathcal Q^{-1}\mathcal S>0$;
--   2. $\mathcal R>0$ and $\mathcal Q-\mathcal S\mathcal R^{-1}\mathcal S^{\mathsf T}>0$.
--
--   Here $>0$ means positive definite. This is the strict Schur complement lemma for linear matrix inequalities; in the paper it drives the induction in the proof of Lemma 4.4.
--
--   **Formalization Note** The paper states the lemma for matrices depending on a parameter $x$; the condition is pointwise in $x$, so it is stated for fixed matrices. The inverse is Mathlib's `Matrix.inv`, which returns $0$ for a singular matrix, but on the side of each equivalence where it occurs the inverted block is assumed positive definite, hence invertible. Mathlib currently has only the positive semidefinite version.
-- source:
--   Yu, Chen, Lü, Kurths, Synchronization via pinning control on general complex networks, SIAM J. Control Optim. 51 (2013), p. 1401, Lemma 2.13

import Mathlib

open Matrix

namespace PinningSync.Tree

theorem lemma_2_13 {p q : ℕ} (Q : Matrix (Fin p) (Fin p) ℝ) (S : Matrix (Fin p) (Fin q) ℝ)
    (R : Matrix (Fin q) (Fin q) ℝ) (hQ : Qᵀ = Q) (hR : Rᵀ = R) :
    ((Matrix.fromBlocks Q S Sᵀ R).PosDef ↔ (Q.PosDef ∧ (R - Sᵀ * Q⁻¹ * S).PosDef)) ∧
      ((Matrix.fromBlocks Q S Sᵀ R).PosDef ↔ (R.PosDef ∧ (Q - S * R⁻¹ * Sᵀ).PosDef)) := by sorry

end PinningSync.Tree
