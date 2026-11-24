-- Prove2me | Theorems.Thm_PINNNeuralTangent_output_gradients_stable
-- name    : PINNNeuralTangent.output_gradients_stable
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T10:40:21.267114+00:00
-- url     : https://prove2.me/theorems/c4d3e27b-abe5-4ba6-ac11-ada971f4179b
-- title:
--   Lemma D.4 (as proved): the parameter gradients of $u$ and $u_{xx}$ barely change
-- statement:
--   Assume the setting of Theorem 4.4, with hypothesis (ii) in the form the proof uses (absolute value inside the sums). Then for every $x\in[a,b]$,
--   $$\lim_{N\to\infty}\sup_{t\in[0,T]}\Big\|\frac{\partial u(x,\theta(t))}{\partial\theta}-\frac{\partial u(x,\theta(0))}{\partial\theta}\Big\|_2=0,\qquad \lim_{N\to\infty}\sup_{t\in[0,T]}\Big\|\frac{\partial u_{xx}(x,\theta(t))}{\partial\theta}-\frac{\partial u_{xx}(x,\theta(0))}{\partial\theta}\Big\|_2=0,$$
--   where $\partial/\partial\theta$ is the gradient over all $3N+1$ parameters.
--
--   **Formalization Note** The printed eqs. (D.4)-(D.5) omit "$=0$". The value $0$ is what the proof concludes. Hypothesis (ii) is used in the corrected form, as in Lemma D.2.
-- source:
--   Wang, Yu and Perdikaris, When and why PINNs fail to train: A neural tangent kernel perspective, arXiv:2007.14527v1 (2020), Appendix D, Lemma D.4, eqs. (D.4)-(D.5), pp. 26-28 (under the setting of Theorem 4.4, p. 6)

import Mathlib
import Definitions.Def_PINNNeuralTangent_Basic

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff

namespace PINNNeuralTangent

theorem output_gradients_stable (σ : ℝ → ℝ) (hσ : ActivationBounded4 σ)
    {Nb Nr : ℕ} (a b : ℝ) (xb : Fin Nb → ℝ) (xr : Fin Nr → ℝ) (hdata : IsModelData a b xb xr)
    (g f : ℝ → ℝ) (T : ℝ) (hT : 0 < T) (θ : (N : ℕ) → ℝ → PIdx N → ℝ)
    (hflow : ∀ N, IsGradFlow (modelLoss σ xb xr g f) (θ N) T)
    (h1 : ParamsUnifBounded T θ)
    (h2 : ResidualAbsSumBound σ xb xr g f T θ) :
    ∀ x ∈ Set.Icc a b, ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ t ∈ Set.Icc 0 T,
      l2norm (fun p => pd (fun θ' => netU σ θ' x) (θ N t) p -
        pd (fun θ' => netU σ θ' x) (θ N 0) p) ≤ ε ∧
      l2norm (fun p => pd (fun θ' => netUxx σ θ' x) (θ N t) p -
        pd (fun θ' => netUxx σ θ' x) (θ N 0) p) ≤ ε := by sorry

end PINNNeuralTangent
