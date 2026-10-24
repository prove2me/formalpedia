-- Prove2me | Theorems.Thm_SparseLpLq_SmallP_lemma_2_2
-- name    : SparseLpLq.SmallP.lemma_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:45:57.655039+00:00
-- url     : https://prove2.me/theorems/0a41662a-95e9-4a91-9b99-260ad6db505f
-- title:
--   Lemma 2.2, p. 6 — for 0 < p < 1, minimizers of ‖x‖_p^p over ℙ_j ∩ FEA(A,b,σ,1) are extreme points
-- statement:
--   Assume the blanket assumptions of the paper for $q=1$: $\sigma\ge 0$, $\mathrm{FEA}(A,b,\sigma,1)\ne\emptyset$ and $\|b\|_1>\sigma$. Let $0<p<1$ and let $\mathbb P_j$ be one of the $2^n$ closed orthants of $\mathbb R^n$ (2.2) with $\mathbb P_j\cap\mathrm{FEA}(A,b,\sigma,1)\ne\emptyset$. If $x$ is an optimal solution of
--
--   $$\min_{x\in\mathbb R^n}\ \|x\|_p^p \quad\text{s.t.}\quad x\in\mathbb P_j\cap\mathrm{FEA}(A,b,\sigma,1), \tag{2.3}$$
--
--   that is, $x\in\mathbb P_j\cap\mathrm{FEA}(A,b,\sigma,1)$ and $\|x\|_p^p\le\|y\|_p^p$ for all $y$ in that set, then $x$ is an extreme point of $\mathbb P_j\cap\mathrm{FEA}(A,b,\sigma,1)$.
--
--   Combined with the polyhedrality of $\mathrm{FEA}(A,b,\sigma,1)$ (Lemma C.1), the lemma confines every optimal solution of problem (1.4) with $0<p<1$ to the finitely many extreme points of the $2^n$ pieces $\mathbb P_j\cap\mathrm{FEA}(A,b,\sigma,1)$; this is the basis of Proposition 2.1.
--
--   **Formalization Note** The orthant $\mathbb P_j$ is indexed by a sign pattern `s : Fin n → Bool`. Extreme points are Mathlib's `Set.extremePoints ℝ`.
--
--   Differences from the source:
--   - encoding: orthant index j ∈ {1, …, 2ⁿ} → sign pattern s : Fin n → Bool (true: xᵢ ≥ 0, false: xᵢ ≤ 0); reason: the sign patterns enumerate the 2ⁿ closed orthants of (2.2) one-to-one
-- source:
--   Yang, Chen & Xiang, Sparse solutions of a class of constrained optimization problems, arXiv:1907.00880v5, p. 6, Lemma 2.2 (problem (2.3), orthants (2.2)); proof p. 7

import Mathlib
import Definitions.Def_SparseLpLq_SmallP_Setting

open scoped ENNReal Matrix

namespace SparseLpLq.SmallP
theorem lemma_2_2 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (σ : ℝ)
    (hσ : 0 ≤ σ) (hfeas : (FEA A b σ 1).Nonempty) (hb : σ < qNorm 1 b)
    (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) (s : Fin n → Bool)
    (hne : (orthant s ∩ FEA A b σ 1).Nonempty)
    (x : Fin n → ℝ) (hx : x ∈ orthant s ∩ FEA A b σ 1)
    (hopt : ∀ y ∈ orthant s ∩ FEA A b σ 1, lpObj p x ≤ lpObj p y) :
    x ∈ Set.extremePoints ℝ (orthant s ∩ FEA A b σ 1) := by sorry
end SparseLpLq.SmallP
