-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_rank3_gaussian_rounding_quintic
-- name    : QuantumMaxCutEnergy.rank3_gaussian_rounding_quintic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T02:30:23.158264+00:00
-- url     : https://prove2.me/theorems/33c093e3-8431-48e7-adbf-fdc314f06a3b
-- title:
--   Rank-three Gaussian rounding with real weights and a three-term bound on $E_3$
-- statement:
--   Let $X$ be a real positive semidefinite $n\times n$ matrix with unit diagonal and let $a_{ij}\ge 0$ be real weights on the pairs $i<j$. Then there are unit vectors $r_1,\dots,r_n\in\mathbb R^3$ with
--
--   $$\sum_{i<j}a_{ij}\,\langle r_i,r_j\rangle\le\sum_{i<j}a_{ij}\,\varphi(X_{ij}),\qquad \varphi(t)=\begin{cases}0.84882\,t+0.084882\,t^3+0.027283\,t^5,&t\le 0,\\ t,&t>0.\end{cases}$$
--
--   The constants are lower bounds for the first three coefficients $\frac{8}{3\pi}$, $\frac{4}{15\pi}$, $\frac{3}{35\pi}$ of the rank-three rounding function $E_3$.
-- source:
--   Briët, de Oliveira Filho and Vallentin, Grothendieck inequalities for semidefinite programs with rank constraint, Theory of Computing 10(4), 2014, Lemma 2.1 and Eq. (2.1) with r = 3; used with reweighted edges in Apte, Lee, Marwaha, Parekh and Sud, ESA 2025, https://doi.org/10.4230/LIPIcs.ESA.2025.101, Eqs. (17)-(18).

import Mathlib
import Definitions.Def_QuantumMaxCutEnergyEstimationModel

open scoped BigOperators

theorem QuantumMaxCutEnergy.rank3_gaussian_rounding_quintic (n : ℕ)
    (a : QuantumMaxCutEnergy.Edge n → ℝ) (ha : ∀ e, 0 ≤ a e)
    (X : Matrix (Fin n) (Fin n) ℝ) (hX : X.PosSemidef) (hdiag : ∀ i, X i i = 1) :
    ∃ r : Fin n → Fin 3 → ℝ,
      (∀ i, ∑ b : Fin 3, (r i b) ^ 2 = 1) ∧
      (∑ e : QuantumMaxCutEnergy.Edge n, a e *
          (∑ b : Fin 3, r e.val.1 b * r e.val.2 b)) ≤
        ∑ e : QuantumMaxCutEnergy.Edge n, a e *
          (if X e.val.1 e.val.2 ≤ 0 then
            0.84882 * X e.val.1 e.val.2 + 0.084882 * (X e.val.1 e.val.2) ^ 3 +
              0.027283 * (X e.val.1 e.val.2) ^ 5
          else X e.val.1 e.val.2) := by sorry
