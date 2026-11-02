-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_agm_rank3_gaussian_rounding
-- name    : QuantumMaxCutEnergy.agm_rank3_gaussian_rounding
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-01T17:00:26.50218+00:00
-- url     : https://prove2.me/theorems/9ed74a37-1721-48f0-95d6-3777ba1d8ba1
-- title:
--   Rank-three Gaussian rounding of a Max-Cut SDP solution (BOV 2014, Lemma 2.1)
-- statement:
--   Let $G$ be a graph on $n$ vertices with nonnegative edge weights $w$, and let $X$ be a real positive semidefinite matrix of order $n$ with $X_{ii}=1$ for all $i$, i.e. a feasible point of the Goemans--Williamson Max-Cut semidefinite relaxation. Then there are unit vectors $r_1,\dots,r_n\in\mathbb R^3$ such that
--
--   $$\sum_{\{i,j\}} w_{ij}\,(r_i\cdot r_j)\;\le\;0.046\sum_{\{i,j\}} w_{ij}\;+\;0.954\sum_{\{i,j\}} w_{ij}\,X_{ij}.$$
--
--   In words: a rank-three (Bloch-vector) correlation can pay $0.954$ of the SDP correlation, up to the explicit slack $0.046$ times the total weight. This is the rank-three Gaussian rounding inequality behind Theorem 1 of Anshu--Gosset--Morenz. Write $X=UU^{\mathsf T}$ with rows $U_i$, draw a random $3\times n$ matrix $R$ of independent standard Gaussians and set $r_i=R U_i/\lVert R U_i\rVert$. Then $\mathbb E[r_i\cdot r_j]=F(3,X_{ij})$ with
--
--   $$F(3,t)=\frac{2}{3}\Big(\frac{\Gamma(2)}{\Gamma(3/2)}\Big)^2 t\,{}_2F_1\!\Big(\begin{smallmatrix}1/2,1/2\\ 5/2\end{smallmatrix};t^2\Big)=\frac{8}{3\pi}\sum_{k\ge0}\frac{(1/2)_k^2}{(5/2)_k\,k!}t^{2k+1},$$
--
--   a series with nonnegative coefficients that sum to one and whose first two coefficients are $c_0=8/(3\pi)$ and $c_1=4/(15\pi)$; hence $F(3,t)\le 0.046+0.954t$ on $[-1,1]$ by the positive-series scalar certificate. Averaging over $R$ and using $w_{ij}\ge0$ gives the claim for some realisation of the rounding. No rounding sampler, state preparation or numerical solver is asserted here: this is the analytic integrality-gap statement only.
-- source:
--   Briët, de Oliveira Filho and Vallentin, Theory of Computing 10(4), 2014, Lemma 2.1 (matrix Grothendieck identity), https://doi.org/10.4086/toc.2014.v010a004 ; the rank-three integrality-gap statement used as Theorem 1 in Anshu, Gosset and Morenz, TQC 2020, https://doi.org/10.4230/LIPIcs.TQC.2020.7 ; scalar positive-series certificate as in Gharibian and Parekh, APPROX/RANDOM 2019, Appendix C Lemma 10, https://doi.org/10.4230/LIPIcs.APPROX-RANDOM.2019.31 (platform theorem QuantumMaxCutEnergy.rank3_odd_series_ratio_0954).

import Mathlib
import Definitions.Def_QuantumMaxCutEnergyEstimationModel

open scoped BigOperators

theorem QuantumMaxCutEnergy.agm_rank3_gaussian_rounding (n : ℕ) (w : QuantumMaxCutEnergy.Weights n)
    (X : Matrix (Fin n) (Fin n) ℝ) (hX : X.PosSemidef) (hdiag : ∀ i, X i i = 1) :
    ∃ r : Fin n → Fin 3 → ℝ,
      (∀ i, ∑ a : Fin 3, (r i a) ^ 2 = 1) ∧
      (∑ e : QuantumMaxCutEnergy.Edge n, (w e : ℝ) *
          (∑ a : Fin 3, r e.val.1 a * r e.val.2 a)) ≤
        0.046 * (∑ e : QuantumMaxCutEnergy.Edge n, (w e : ℝ)) +
          0.954 * (∑ e : QuantumMaxCutEnergy.Edge n, (w e : ℝ) * X e.val.1 e.val.2) := by sorry
