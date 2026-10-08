-- Prove2me | Theorems.Thm_PCSPBLPAff_Symmetric_W_nonneg_sum
-- name    : PCSPBLPAff.Symmetric.W_nonneg_sum
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:03:11.83124+00:00
-- url     : https://prove2.me/theorems/4b96c6aa-e6a6-45f4-a292-c2df75b7b304
-- title:
--   Proof of Theorem 2, pp. 6–7 — W_i(a) = uℓw_i(a) + vr_i(a) are non-negative integers which sum to L
-- statement:
--   Let $(w,p)$ be a solution of $\mathrm{LP}_{\mathbb Q}(X,\mathbf A)$ and $(r,q)$ a solution of $\mathrm{Aff}_{\mathbb Z}(X,\mathbf A)$ with $r_i(a)=0$ whenever $w_i(a)=0$. Let $\ell\ge1$ be an integer with $\ell\,w_i(a)\in\mathbb Z$ for all $i,a$, and $M\in\mathbb N$ with $|r_i(a)|\le M$ for all $i,a$. Let $L=u\ell+v$ with $u,v\in\mathbb N$, $v\le\ell-1$ and $L\ge M\ell^2$. Then for every variable $x_i$ the numbers
--   $$
--   W_i(a) := u\ell\,w_i(a) + v\,r_i(a)\qquad(a\in A)
--   $$
--   are non-negative integers with $\sum_{a\in A}W_i(a)=L$.
--
--   These counts determine the input $(\dots,a,\dots,a,\dots)$, with $a$ repeated $W_i(a)$ times, that is fed to a symmetric polymorphism of arity $L$ to define the value of $x_i$ in $\mathbf B$.
--
--   **Formalization Note** The paper takes $\ell$ to be the least common denominator of the LP solution and $M$ the maximum absolute value in the affine solution; the statement holds for any common denominator and any bound, of which these are instances. The conclusion gives $W_i$ as a function $A\to\mathbb N$ whose rational values equal the displayed formula.
-- source:
--   arXiv:1907.04383v3, proof of Theorem 2, pp. 6–7, from "For each i ∈ [n] and a ∈ A, let" to "non-negative integers which sum to L"

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting

namespace PCSPBLPAff.Symmetric

/-- Proof of Theorem 2, pp. 6–7: for a common denominator `ℓ` of the LP solution, a bound `M`
on the affine solution, and `L = uℓ + v ≥ Mℓ²` with `v < ℓ`, the numbers
`W_i(a) = uℓ w_i(a) + v r_i(a)` are non-negative integers which sum to `L`. -/
theorem W_nonneg_sum {τ : Type} {ar : τ → ℕ} {A : Type} [Fintype A] [DecidableEq A]
    (X : Instance τ ar) (𝔸 : RelStruct τ ar A) (w : Fin X.n → A → ℚ)
    (p : (j : Fin X.m) → (Fin (ar (X.sym j)) → A) → ℚ) (r : Fin X.n → A → ℤ)
    (q : (j : Fin X.m) → (Fin (ar (X.sym j)) → A) → ℤ)
    (hLP : IsLPSol X 𝔸 w p) (hAff : IsAffSol X 𝔸 r q) (href : ∀ i a, w i a = 0 → r i a = 0)
    (ℓ : ℕ) (hℓ : 0 < ℓ) (hw : ∀ i a, ∃ z : ℤ, (ℓ : ℚ) * w i a = z)
    (M : ℕ) (hr : ∀ i a, |r i a| ≤ M)
    (u v L : ℕ) (hL : L = u * ℓ + v) (hv : v < ℓ) (hLM : M * ℓ ^ 2 ≤ L) :
    ∀ i, ∃ W : A → ℕ, (∀ a, (W a : ℚ) = u * ℓ * w i a + v * r i a) ∧ ∑ a, W a = L := by sorry

end PCSPBLPAff.Symmetric
