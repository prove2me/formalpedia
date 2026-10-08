-- Prove2me | Theorems.Thm_PCSPBLPAff_Symmetric_P_nonneg_sum
-- name    : PCSPBLPAff.Symmetric.P_nonneg_sum
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:03:20.190612+00:00
-- url     : https://prove2.me/theorems/b63a0026-e4cc-4b8e-8d40-71f7c0c6950d
-- title:
--   Proof of Theorem 2, p. 7 — P_j(y) = uℓp_j(y) + vq_j(y) are non-negative integers which sum to L
-- statement:
--   Let $(w,p)$ be a solution of $\mathrm{LP}_{\mathbb Q}(X,\mathbf A)$ and $(r,q)$ a solution of $\mathrm{Aff}_{\mathbb Z}(X,\mathbf A)$ with $q_j(y)=0$ whenever $p_j(y)=0$. Let $\ell\ge1$ be an integer with $\ell\,p_j(y)\in\mathbb Z$ for all $j,y$, and $M\in\mathbb N$ with $|q_j(y)|\le M$ for all $j,y$. Let $L=u\ell+v$ with $u,v\in\mathbb N$, $v\le\ell-1$ and $L\ge M\ell^2$. Then for every constraint $c_j$ the numbers
--   $$
--   P_j(y) := u\ell\,p_j(y) + v\,q_j(y)\qquad(y\in A^{\mathrm{ar}(R_j)})
--   $$
--   are non-negative integers with $\sum_{y}P_j(y)=L$.
--
--   $P_j(y)$ is the number of rows equal to $y$ in the $L\times\mathrm{ar}(R_j)$ matrix to which the polymorphism is applied.
--
--   **Formalization Note** The page writes "sum to 1"; the display that follows shows the sum is $L$, which is what is stated here. $p_j$ and $q_j$ vanish off $R_j^{\mathbf A}$, so $P_j$ does too and the sum over all tuples equals the sum over $R_j^{\mathbf A}$. As for $W_i$, $\ell$ and $M$ are any common denominator and any bound.
-- source:
--   arXiv:1907.04383v3, proof of Theorem 2, p. 7, from "For every valid assignment y ∈ R_j^A" to "P_j(y) ≥ uℓ(1/ℓ) + v(−M) ≥ Mℓ − ℓM = 0"

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting

namespace PCSPBLPAff.Symmetric

/-- Proof of Theorem 2, p. 7: with `ℓ, M, u, v, L` as for `W_i(a)`, the numbers
`P_j(y) = uℓ p_j(y) + v q_j(y)` are non-negative integers which sum to `L`
(the page prints "sum to 1"). -/
theorem P_nonneg_sum {τ : Type} {ar : τ → ℕ} {A : Type} [Fintype A] [DecidableEq A]
    (X : Instance τ ar) (𝔸 : RelStruct τ ar A) (w : Fin X.n → A → ℚ)
    (p : (j : Fin X.m) → (Fin (ar (X.sym j)) → A) → ℚ) (r : Fin X.n → A → ℤ)
    (q : (j : Fin X.m) → (Fin (ar (X.sym j)) → A) → ℤ)
    (hLP : IsLPSol X 𝔸 w p) (hAff : IsAffSol X 𝔸 r q) (href : ∀ j y, p j y = 0 → q j y = 0)
    (ℓ : ℕ) (hℓ : 0 < ℓ) (hp : ∀ j y, ∃ z : ℤ, (ℓ : ℚ) * p j y = z)
    (M : ℕ) (hq : ∀ j y, |q j y| ≤ M)
    (u v L : ℕ) (hL : L = u * ℓ + v) (hv : v < ℓ) (hLM : M * ℓ ^ 2 ≤ L) :
    ∀ j, ∃ P : (Fin (ar (X.sym j)) → A) → ℕ,
      (∀ y, (P y : ℚ) = u * ℓ * p j y + v * q j y) ∧ ∑ y, P y = L := by sorry

end PCSPBLPAff.Symmetric
