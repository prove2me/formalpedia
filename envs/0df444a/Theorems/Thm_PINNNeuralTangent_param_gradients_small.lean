-- Prove2me | Theorems.Thm_PINNNeuralTangent_param_gradients_small
-- name    : PINNNeuralTangent.param_gradients_small
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T10:18:03.718849+00:00
-- url     : https://prove2.me/theorems/d7e18aef-1db2-42e0-b258-47bed3e3c325
-- title:
--   Lemma D.1: parameter gradients of $u$ and $u_{xx}$ are $O(1/\sqrt N)$
-- statement:
--   Under the setting of Theorem 4.4, as printed, the partial derivatives of $u$ and $u_{xx}$ with respect to the parameters $W^{(0)},W^{(1)},b^{(0)}$ are $O(1/\sqrt N)$ uniformly in time. The setting is: the model problem on $\Omega=(a,b)$, $T>0$, and gradient-flow trajectories $\theta_N(t)$ for every width $N$ satisfying (i), (ii) as printed, and (iii). There are $C$ and $N_0$ such that for all $N\ge N_0$, $t\in[0,T]$, $x\in[a,b]$ and $k=1,\dots,N$,
--   $$\Big|\frac{\partial u(x,\theta_N(t))}{\partial W^{(l)}_k}\Big|,\ \Big|\frac{\partial u(x,\theta_N(t))}{\partial b^{(0)}_k}\Big|,\ \Big|\frac{\partial u_{xx}(x,\theta_N(t))}{\partial W^{(l)}_k}\Big|,\ \Big|\frac{\partial u_{xx}(x,\theta_N(t))}{\partial b^{(0)}_k}\Big|\ \le\ \frac{C}{\sqrt N},\qquad l=0,1.$$
--
--   **Formalization Note** $\|\cdot\|_\infty$ is over the neuron index $k$. The bound is uniform over $x\in[a,b]=\overline\Omega$, as the proof gives it. Hypothesis (ii) is the printed one. The lemma does not use it, nor the gradient flow.
-- source:
--   Wang, Yu and Perdikaris, When and why PINNs fail to train: A neural tangent kernel perspective, arXiv:2007.14527v1 (2020), Appendix D, Lemma D.1, p. 23 (under the setting of Theorem 4.4, Section 4, p. 6)

import Mathlib
import Definitions.Def_PINNNeuralTangent_Basic

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff

namespace PINNNeuralTangent

theorem param_gradients_small (σ : ℝ → ℝ) (hσ : ActivationBounded4 σ)
    {Nb Nr : ℕ} (a b : ℝ) (xb : Fin Nb → ℝ) (xr : Fin Nr → ℝ) (hdata : IsModelData a b xb xr)
    (g f : ℝ → ℝ) (T : ℝ) (hT : 0 < T) (θ : (N : ℕ) → ℝ → PIdx N → ℝ)
    (hflow : ∀ N, IsGradFlow (modelLoss σ xb xr g f) (θ N) T)
    (h1 : ParamsUnifBounded T θ)
    (h2 : ResidualSumBound σ xb xr g f T θ) :
    ∃ (C : ℝ) (N₀ : ℕ), ∀ N ≥ N₀, ∀ t ∈ Set.Icc 0 T, ∀ x ∈ Set.Icc a b, ∀ k : Fin N,
      |pd (fun θ' => netU σ θ' x) (θ N t) (idxW0 k)| ≤ C / Real.sqrt N ∧
      |pd (fun θ' => netU σ θ' x) (θ N t) (idxW1 k)| ≤ C / Real.sqrt N ∧
      |pd (fun θ' => netU σ θ' x) (θ N t) (idxB0 k)| ≤ C / Real.sqrt N ∧
      |pd (fun θ' => netUxx σ θ' x) (θ N t) (idxW0 k)| ≤ C / Real.sqrt N ∧
      |pd (fun θ' => netUxx σ θ' x) (θ N t) (idxW1 k)| ≤ C / Real.sqrt N ∧
      |pd (fun θ' => netUxx σ θ' x) (θ N t) (idxB0 k)| ≤ C / Real.sqrt N := by sorry

end PINNNeuralTangent
