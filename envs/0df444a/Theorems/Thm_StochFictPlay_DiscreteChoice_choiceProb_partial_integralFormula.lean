-- Prove2me | Theorems.Thm_StochFictPlay_DiscreteChoice_choiceProb_partial_integralFormula
-- name    : StochFictPlay.DiscreteChoice.choiceProb_partial_integralFormula
-- status  : Open
-- author  : @junyihjy
-- created : 2026-10-01T16:46:06.160787+00:00
-- url     : https://prove2.me/theorems/2909aa47-eb7c-4ad0-b4f9-0f240f3e3e8a
-- title:
--   Eq. (4): integral representation of the off-diagonal choice-probability partials
-- statement:
--   Let $\varepsilon$ have a continuous, everywhere strictly positive density $f$ on $\mathbb{R}^n$, and let $C : \mathbb{R}^n \to \mathbb{R}^n$ be the choice probability function $C_i(\pi) = P(\operatorname{argmax}_j \pi_j + \varepsilon_j = i)$ of the additive random utility model. Assume $C$ is continuously differentiable. Then for every payoff vector $\pi$ and every pair of distinct alternatives $i \neq j$,
--
--   $$\frac{\partial C_i}{\partial \pi_j}(\pi) = -\int_{\{x : \pi_k + x_k < \pi_i + x_i\ \forall k \neq i,j\}} f(x_1, \ldots, x_{j-1}, \pi_i + x_i - \pi_j, x_{j+1}, \ldots, x_n)\, dx_{-j},$$
--
--   the $(n-1)$-fold integral of the density over the face where $i$ and $j$ tie for the maximum, with the $j$-th coordinate pinned at $\hat{x}_j = \pi_i + x_i - \pi_j$ (the change of variables of Hofbauer–Sandholm (2002), eq. (4), p. 6). Since $f > 0$ everywhere, the integral is strictly positive and the off-diagonal partial is strictly negative; exchanging the roles of $i$ and $j$ gives the symmetry $\partial C_i / \partial \pi_j = \partial C_j / \partial \pi_i$. This is the deep analytic input behind the symmetry/negativity of the derivative matrix $DC(\pi)$ (Theorem 2.1 of Hofbauer–Sandholm 2002), mission-connected as a child of the Thm 2.1 leaf `exists_admissible_perturbation` (d555a301) and the stated bridge used by `dC_symm_offdiag_neg` (131ee9c1).
-- source:
--   Hofbauer, J. and Sandholm, W. H., 'On the Global Convergence of Stochastic Fictitious Play', Econometrica 70(6), 2002, eq. (4), p. 6

import Mathlib

namespace StochFictPlay.DiscreteChoice

/-- `f : ℝⁿ → ℝ` is a strictly positive probability density of the utility-shock vector
`ε = (ε₁, …, εₙ)`: it is continuous, strictly positive at every point, and integrates to one
against Lebesgue measure. Continuity is how the formula (4) of Hofbauer–Sandholm (2002),
which evaluates `f` on hyperplanes, is read. -/
structure IsStrictlyPositiveDensity {n : ℕ} (f : (Fin n → ℝ) → ℝ) : Prop where
  continuous : Continuous f
  pos : ∀ x, 0 < f x
  lintegral_eq_one :
    MeasureTheory.lintegral MeasureTheory.volume (fun x => ENNReal.ofReal (f x)) = 1

/-- The law of the shock vector `ε` with density `f`: Lebesgue measure on `ℝⁿ` weighted by `f`. -/
noncomputable def noiseLaw {n : ℕ} (f : (Fin n → ℝ) → ℝ) : MeasureTheory.Measure (Fin n → ℝ) :=
  MeasureTheory.Measure.withDensity MeasureTheory.volume (fun x => ENNReal.ofReal (f x))

/-- The choice probability function (1) of the additive random utility model,
`Cᵢ(π) = P(argmaxⱼ πⱼ + εⱼ = i)`: the probability, under the law of `ε`, that alternative `i`
has strictly the highest total payoff `πᵢ + εᵢ`. Ties have probability zero because `ε` has a
density. Hofbauer–Sandholm (2002), p. 4, eq. (1). -/
noncomputable def choiceProb {n : ℕ} (f : (Fin n → ℝ) → ℝ) (π : Fin n → ℝ) (i : Fin n) : ℝ :=
  (noiseLaw f {e | ∀ j, j ≠ i → π j + e j < π i + e i}).toReal

end StochFictPlay.DiscreteChoice

namespace StochFictPlay.DiscreteChoice

/-- Eq. (4) (Hofbauer–Sandholm 2002, p. 6): for `i ≠ j`, the off-diagonal partial
`∂Cᵢ/∂πⱼ(π)` is the negative of the `(n - 1)`-fold integral of the shock density `f`
over the face where alternatives `i` and `j` tie for the maximum. The integral evaluates
`f` at the tie point `x j = π i + x i - π j` — the change of variables
`x̂ⱼ = πᵢ + xᵢ - πⱼ` that moves the moving boundary of `Cᵢ` onto the fixed
hyperplane where `i` and `j` are tied — and integrates over Lebesgue measure restricted
to `{x | π k + x k < π i + x i for all k ≠ i, j}`. Since `f > 0` everywhere, the
integral is strictly positive, so the partial is strictly negative. This is the deep
analytic input behind `dC_symm_offdiag_neg` (symmetry `∂Cᵢ/∂πⱼ = ∂Cⱼ/∂πᵢ` follows by
exchanging the roles of `i` and `j` in the same integral representation). -/
theorem choiceProb_partial_integralFormula {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (hf : IsStrictlyPositiveDensity f)
    (hC : ContDiff ℝ 1 (choiceProb f)) (π : Fin n → ℝ) (i j : Fin n) (hij : i ≠ j) :
    fderiv ℝ (choiceProb f) π (Pi.single j 1) i =
      -MeasureTheory.integral
        (MeasureTheory.Measure.restrict MeasureTheory.volume
          {x : Fin n → ℝ | ∀ k : Fin n, k ≠ i → k ≠ j → π k + x k < π i + x i})
        (fun x : Fin n → ℝ => f (Function.update x j (π i + x i - π j))) := by sorry

end StochFictPlay.DiscreteChoice
