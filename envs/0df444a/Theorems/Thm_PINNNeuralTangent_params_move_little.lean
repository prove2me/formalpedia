-- Prove2me | Theorems.Thm_PINNNeuralTangent_params_move_little
-- name    : PINNNeuralTangent.params_move_little
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T10:22:27.622786+00:00
-- url     : https://prove2.me/theorems/205ffe87-ba5b-427b-b5e7-331a4ef0c10d
-- title:
--   Lemma D.2 (as proved, hypothesis (ii) with $|\cdot|$ inside the sum): the parameters change little
-- statement:
--   Assume the setting of Theorem 4.4, with hypothesis (ii) in the form the proof uses: $\int_0^T\sum_i|u(x_b^i,\theta_N(\tau))-g(x_b^i)|\,d\tau\le C$ and $\int_0^T\sum_j|u_{xx}(x_r^j,\theta_N(\tau))-f(x_r^j)|\,d\tau\le C$ for all $N$. Then
--   $$\lim_{N\to\infty}\sup_{t\in[0,T]}\Big\|\frac1{\sqrt N}\big(W^{(l)}(t)-W^{(l)}(0)\big)\Big\|_2=0\ (l=0,1),\qquad \lim_{N\to\infty}\sup_{t\in[0,T]}\Big\|\frac1{\sqrt N}\big(b^{(0)}(t)-b^{(0)}(0)\big)\Big\|_2=0.$$
--
--   **Formalization Note** This is the statement as proved. With (ii) as printed, with the absolute value outside the sums, the lemma is false. Take $\sigma=\tanh$, $\Omega=(-1,1)$, $x_b=\pm1$, $x_r=\pm\frac12$, $g=f=0$, and start from $W^{(0)}_k=W^{(1)}_k=1$, $b=0$. By oddness the residual sums vanish identically. Every neuron follows the same $N$-independent ODE, so $\|(W^{(0)}(t)-W^{(0)}(0))/\sqrt N\|_2$ does not depend on $N$. The step of the proof that fails bounds $|\sum_i r_i\,\partial u(x_b^i)/\partial W_k|$ by $\|\partial u/\partial W\|_\infty|\sum_ir_i|$. The limit is written with explicit $\varepsilon$ and $N_0$.
-- source:
--   Wang, Yu and Perdikaris, When and why PINNs fail to train: A neural tangent kernel perspective, arXiv:2007.14527v1 (2020), Appendix D, Lemma D.2, eqs. (D.1)-(D.2), pp. 24-25 (under the setting of Theorem 4.4, p. 6)

import Mathlib
import Definitions.Def_PINNNeuralTangent_Basic

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff

namespace PINNNeuralTangent

theorem params_move_little (σ : ℝ → ℝ) (hσ : ActivationBounded4 σ)
    {Nb Nr : ℕ} (a b : ℝ) (xb : Fin Nb → ℝ) (xr : Fin Nr → ℝ) (hdata : IsModelData a b xb xr)
    (g f : ℝ → ℝ) (T : ℝ) (hT : 0 < T) (θ : (N : ℕ) → ℝ → PIdx N → ℝ)
    (hflow : ∀ N, IsGradFlow (modelLoss σ xb xr g f) (θ N) T)
    (h1 : ParamsUnifBounded T θ)
    (h2 : ResidualAbsSumBound σ xb xr g f T θ) :
    ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ t ∈ Set.Icc 0 T,
      l2norm (fun k : Fin N => (θ N t (idxW0 k) - θ N 0 (idxW0 k)) / Real.sqrt N) ≤ ε ∧
      l2norm (fun k : Fin N => (θ N t (idxW1 k) - θ N 0 (idxW1 k)) / Real.sqrt N) ≤ ε ∧
      l2norm (fun k : Fin N => (θ N t (idxB0 k) - θ N 0 (idxB0 k)) / Real.sqrt N) ≤ ε := by sorry

end PINNNeuralTangent
