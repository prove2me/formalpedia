-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_rank3_gaussian_rounding_cubic
-- name    : QuantumMaxCutEnergy.rank3_gaussian_rounding_cubic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T15:19:15.221216+00:00
-- url     : https://prove2.me/theorems/89bc291d-1674-4f21-9d7e-37cb59626375
-- title:
--   Rank-three Gaussian rounding with the cubic bound on $E_3$
-- statement:
--   Let $X$ be a real positive semidefinite $n\times n$ matrix with unit diagonal and let $w$ be nonnegative rational weights on the pairs $i<j$. Then there are unit vectors $r_1,\dots,r_n\in\mathbb R^3$ with
--
--   $$\sum_{i<j}w_{ij}\,\langle r_i,r_j\rangle\le\sum_{i<j}w_{ij}\,\varphi(X_{ij}),\qquad \varphi(t)=\begin{cases}0.8488\,t+0.08488\,t^3,&t\le 0,\\ t,&t>0.\end{cases}$$
--
--   This is the rank-three rounding of Briët, de Oliveira Filho and Vallentin: the expected correlation is $E_3(X_{ij})$, an odd power series with nonnegative coefficients summing to $1$ whose first two coefficients are $8/(3\pi)\ge 0.8488$ and $4/(15\pi)\ge 0.08488$, so $E_3\le\varphi$ on $[-1,1]$.
-- source:
--   Briët, de Oliveira Filho and Vallentin, Grothendieck inequalities for semidefinite programs with rank constraint, Theory of Computing 10(4), 2014, Lemma 2.1 and Eq. (2.1) with r = 3; Gharibian and Parekh, APPROX 2019, product-state rounding; Lee and Parekh, ICALP 2024, https://doi.org/10.4230/LIPIcs.ICALP.2024.105, Eq. (8).

import Mathlib
import Definitions.Def_QuantumMaxCutEnergyEstimationModel

open scoped BigOperators

theorem QuantumMaxCutEnergy.rank3_gaussian_rounding_cubic (n : ℕ)
    (w : QuantumMaxCutEnergy.Weights n)
    (X : Matrix (Fin n) (Fin n) ℝ) (hX : X.PosSemidef) (hdiag : ∀ i, X i i = 1) :
    ∃ r : Fin n → Fin 3 → ℝ,
      (∀ i, ∑ a : Fin 3, (r i a) ^ 2 = 1) ∧
      (∑ e : QuantumMaxCutEnergy.Edge n, (w e : ℝ) *
          (∑ a : Fin 3, r e.val.1 a * r e.val.2 a)) ≤
        ∑ e : QuantumMaxCutEnergy.Edge n, (w e : ℝ) *
          (if X e.val.1 e.val.2 ≤ 0 then
            0.8488 * X e.val.1 e.val.2 + 0.08488 * (X e.val.1 e.val.2) ^ 3
          else X e.val.1 e.val.2) := by sorry
