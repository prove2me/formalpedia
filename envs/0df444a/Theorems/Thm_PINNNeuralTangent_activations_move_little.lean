-- Prove2me | Theorems.Thm_PINNNeuralTangent_activations_move_little
-- name    : PINNNeuralTangent.activations_move_little
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T10:30:06.412395+00:00
-- url     : https://prove2.me/theorems/620a7c41-98a3-4f39-8ec7-c8d516a737a5
-- title:
--   Lemma D.3 (as proved): the hidden activations and their derivatives change little
-- statement:
--   Assume the setting of Theorem 4.4, with hypothesis (ii) in the form the proof uses (absolute value inside the sums). Then for every $x\in[a,b]$ and $k=0,1,2,3$,
--   $$\lim_{N\to\infty}\sup_{t\in[0,T]}\Big\|\frac1{\sqrt N}\Big(\sigma^{(k)}\big(W^{(0)}(t)x+b^{(0)}(t)\big)-\sigma^{(k)}\big(W^{(0)}(0)x+b^{(0)}(0)\big)\Big)\Big\|_2=0,$$
--   with $\sigma^{(k)}$ applied coordinatewise.
--
--   **Formalization Note** This is the statement as proved. The printed eq. (D.3) has $W^{(0)}(t)$ in the second term. The first line of the proof and the later use in Lemma D.4 have $W^{(0)}(0)$, and that version is stated. Hypothesis (ii) is used in the corrected form, as in Lemma D.2.
-- source:
--   Wang, Yu and Perdikaris, When and why PINNs fail to train: A neural tangent kernel perspective, arXiv:2007.14527v1 (2020), Appendix D, Lemma D.3, eq. (D.3), p. 25 (under the setting of Theorem 4.4, p. 6)

import Mathlib
import Definitions.Def_PINNNeuralTangent_Basic

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff

namespace PINNNeuralTangent

theorem activations_move_little (σ : ℝ → ℝ) (hσ : ActivationBounded4 σ)
    {Nb Nr : ℕ} (a b : ℝ) (xb : Fin Nb → ℝ) (xr : Fin Nr → ℝ) (hdata : IsModelData a b xb xr)
    (g f : ℝ → ℝ) (T : ℝ) (hT : 0 < T) (θ : (N : ℕ) → ℝ → PIdx N → ℝ)
    (hflow : ∀ N, IsGradFlow (modelLoss σ xb xr g f) (θ N) T)
    (h1 : ParamsUnifBounded T θ)
    (h2 : ResidualAbsSumBound σ xb xr g f T θ) :
    ∀ x ∈ Set.Icc a b, ∀ k ≤ 3, ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ t ∈ Set.Icc 0 T,
      l2norm (fun j : Fin N =>
        (iteratedDeriv k σ (θ N t (idxW0 j) * x + θ N t (idxB0 j)) -
          iteratedDeriv k σ (θ N 0 (idxW0 j) * x + θ N 0 (idxB0 j))) / Real.sqrt N) ≤ ε := by sorry

end PINNNeuralTangent
