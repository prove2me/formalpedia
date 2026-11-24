-- Prove2me | Theorems.Thm_PINNNeuralTangent_ntk_constant_during_training
-- name    : PINNNeuralTangent.ntk_constant_during_training
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T10:51:31.006844+00:00
-- url     : https://prove2.me/theorems/50a3ae62-d991-4ac3-a1db-003901beb876
-- title:
--   Theorem 4.4 (as proved, hypothesis (ii) with $|\cdot|$ inside the sum): the NTK of a wide PINN stays constant during training
-- statement:
--   Take the model problem $u_{xx}=f$ on $\Omega=(a,b)$, $u=g$ on $\{a,b\}$, with boundary points $x_b^i\in\{a,b\}$ and collocation points $x_r^j\in(a,b)$. Let $T>0$, and for every width $N$ let $\theta_N(t)$, $t\in[0,T]$, be a gradient-flow trajectory of the PINN loss of the one-hidden-layer network. Assume:
--   1. there is $C>0$, independent of $N$, with $\sup_{t\in[0,T]}\|\theta_N(t)\|_\infty\le C$;
--   2. there is $C>0$, independent of $N$, with $\int_0^T\sum_{i=1}^{N_b}|u(x_b^i,\theta_N(\tau))-g(x_b^i)|\,d\tau\le C$ and $\int_0^T\sum_{j=1}^{N_r}|u_{xx}(x_r^j,\theta_N(\tau))-f(x_r^j)|\,d\tau\le C$;
--   3. $\sigma$ is smooth and $|\sigma^{(k)}|\le C$ for $k=0,1,2,3,4$.
--
--   Then
--   $$\lim_{N\to\infty}\sup_{t\in[0,T]}\|K(t)-K(0)\|_2=0,$$
--   where $K(t)$ is the NTK of the PINN at $\theta_N(t)$ and $\|\cdot\|_2$ is the spectral norm.
--
--   This is the paper's key result: during training, a sufficiently wide PINN behaves like a kernel method with a fixed kernel.
--
--   **Formalization Note** This is the statement as proved. The printed hypothesis (ii) puts the absolute value outside the sums, $\int_0^T|\sum_i(\cdots)|\,d\tau\le C$. With that hypothesis the theorem is false. In the odd, symmetric counterexample described under Lemma D.2, both sums vanish identically, (i) holds with $C=1$, and $\sup_t\|K(t)-K(0)\|_2\approx7.75$ for every $N$. The proof bounds $|\sum_ir_i\,\partial u(x_b^i)/\partial W_k|$ by $\|\partial u/\partial W\|_\infty\,|\sum_ir_i|$, which is valid only with the absolute value inside the sum. The paper does not state the initialization in this theorem. Under random $\mathcal N(0,1)$ initialization, hypothesis (i) fails almost surely for large $N$, because $\max_k|W_k(0)|$ grows like $\sqrt{2\log N}$. So the theorem is stated for deterministic families of trajectories, which is what the proof uses. The limit is written with explicit $\varepsilon$ and $N_0$.
-- source:
--   Wang, Yu and Perdikaris, When and why PINNs fail to train: A neural tangent kernel perspective, arXiv:2007.14527v1 (2020), Section 4, Theorem 4.4, eq. (4.8), p. 6; proof in Appendix D, pp. 23-28

import Mathlib
import Definitions.Def_PINNNeuralTangent_Basic

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff

namespace PINNNeuralTangent

theorem ntk_constant_during_training (σ : ℝ → ℝ) (hσ : ActivationBounded4 σ)
    {Nb Nr : ℕ} (a b : ℝ) (xb : Fin Nb → ℝ) (xr : Fin Nr → ℝ) (hdata : IsModelData a b xb xr)
    (g f : ℝ → ℝ) (T : ℝ) (hT : 0 < T) (θ : (N : ℕ) → ℝ → PIdx N → ℝ)
    (hflow : ∀ N, IsGradFlow (modelLoss σ xb xr g f) (θ N) T)
    (h1 : ParamsUnifBounded T θ)
    (h2 : ResidualAbsSumBound σ xb xr g f T θ) :
    ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ t ∈ Set.Icc 0 T,
      specNorm (modelNTK σ xb xr (θ N t) - modelNTK σ xb xr (θ N 0)) ≤ ε := by sorry

end PINNNeuralTangent
