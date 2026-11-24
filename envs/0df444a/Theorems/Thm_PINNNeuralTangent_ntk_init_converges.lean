-- Prove2me | Theorems.Thm_PINNNeuralTangent_ntk_init_converges
-- name    : PINNNeuralTangent.ntk_init_converges
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T10:14:30.215275+00:00
-- url     : https://prove2.me/theorems/2419a3ba-e3b9-49f3-8e66-9966aee8ce85
-- title:
--   Theorem 4.3 (as proved): the NTK of a PINN at initialization converges in probability
-- statement:
--   Let $\sigma$ be smooth and let $\sigma,\dot\sigma,\ddot\sigma,\dddot\sigma$ grow at most polynomially: $|\sigma^{(k)}(z)|\le C(1+|z|^m)$ for $k\le3$. Take the model problem on $\Omega=(a,b)$ with boundary points $x_b^i\in\{a,b\}$ and collocation points $x_r^j\in(a,b)$. Let $K(0)$ be the NTK of the one-hidden-layer PINN of width $N$ at the i.i.d. $\mathcal N(0,1)$ initialization. Then, as $N\to\infty$, $K(0)$ converges in probability to the deterministic matrix
--   $$K^*=\begin{bmatrix}\Theta_{uu}^{(1)}&\Theta_{ur}^{(1)}\\\Theta_{ru}^{(1)}&\Theta_{rr}^{(1)}\end{bmatrix}.$$
--   That is, for every entry $(i,j)$ and every $\varepsilon>0$, $\Pr\big(|K(0)_{ij}-K^*_{ij}|\ge\varepsilon\big)\to0$. Here $\Theta_{uu},\Theta_{ur},\Theta_{rr}$ are the Gaussian expectations in the definitions (Appendix C), and $\Theta_{ru}(x,x')=\Theta_{ur}(x',x)$.
--
--   **Formalization Note** This is the statement as proved. The law-of-large-numbers steps of Appendix C determine each limit, but several printed closed forms differ from them. In $\Theta_{rr}$ the factors $2$, $2$, $4$ of $J_2,J_3,J_4$ are dropped. $B_{rr}$ and $B_{ur}$ evaluate the second factor at $x$ instead of $x'$. $C_{ur}$ squares $\dot\sigma\dddot\sigma$. With $\Sigma^{(1)}$ as defined in eq. (2.4), the printed $\Theta_{uu}$ counts the constant $1$ twice. The paper states no growth condition on $\sigma$. The polynomial-growth hypothesis is added so that the expectations in $K^*$ are finite, which the law of large numbers requires. Convergence of the finite matrix is stated entrywise, which is equivalent.
-- source:
--   Wang, Yu and Perdikaris, When and why PINNs fail to train: A neural tangent kernel perspective, arXiv:2007.14527v1 (2020), Section 4, Theorem 4.3, eq. (4.7), p. 6; limit K* computed in Appendix C, pp. 20-23

import Mathlib
import Definitions.Def_PINNNeuralTangent_Basic

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff

namespace PINNNeuralTangent

theorem ntk_init_converges (σ : ℝ → ℝ) (hσ : ContDiff ℝ ∞ σ)
    (hgrowth : ∃ (C : ℝ) (m : ℕ), ∀ k ≤ 3, ∀ z, |iteratedDeriv k σ z| ≤ C * (1 + |z| ^ m))
    {Nb Nr : ℕ} (a b : ℝ) (xb : Fin Nb → ℝ) (xr : Fin Nr → ℝ) (hdata : IsModelData a b xb xr) :
    ∀ i j, ∀ ε > 0,
      Tendsto (fun N : ℕ => initMeasure N
          {θ | ε ≤ |modelNTK σ xb xr θ i j - limitNTK σ xb xr i j|}) atTop (𝓝 0) := by sorry

end PINNNeuralTangent
