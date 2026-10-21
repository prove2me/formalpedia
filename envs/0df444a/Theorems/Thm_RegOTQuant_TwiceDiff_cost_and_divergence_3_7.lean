-- Prove2me | Theorems.Thm_RegOTQuant_TwiceDiff_cost_and_divergence_3_7
-- name    : RegOTQuant.TwiceDiff.cost_and_divergence_3_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:39:03.782159+00:00
-- url     : https://prove2.me/theorems/92fc9703-cf78-4bcd-9bc2-592c39c43986
-- title:
--   Display (3.7), p. 16, corrected — quantized cost and divergence bounds
-- statement:
--   Suppose the hypotheses of Theorem 3.8 hold and $f$ satisfies the standing divergence conditions. For every integer $n\ge1$, there are $\widetilde\pi\in\mathcal P^n(X)$ and $\pi\in\Pi(\mu_1,\ldots,\mu_N)$ such that
--
--   $$
--   \int c\,d\pi-\int c\,d\pi^*\le 2BC^2n^{-2\alpha},
--   \qquad D_f(\pi,P)\le D_f\left(\widetilde\pi,\bigotimes_i\mu_i^n\right).
--   $$
--
--   The first estimate is the corrected form of (3.7): the paper prints $2BCn^{-2\alpha}$, but its $W_2$ quantization assumption yields $C^2$. The second estimate is the data-processing display immediately following (3.7).
-- source:
--   Eckstein & Nutz, Convergence rates for regularized optimal transport via quantization, arXiv:2208.14391v3, p. 16, equation (3.7) and following data-processing display

import Mathlib
import Definitions.Def_RegOTQuant_TwiceDiff_Setting

open MeasureTheory Set

namespace RegOTQuant.TwiceDiff

/-- Display (3.7), p. 16, corrected from 2BC to 2BC², together with the
following data-processing display. -/
theorem cost_and_divergence_3_7 {N : ℕ} {d : Fin N → ℕ}
    (Xs : ∀ i : Fin N, Set (Fi d i)) (μ : ∀ i : Fin N, Measure (Fi d i))
    (c : E d → ℝ) (πs : Measure (E d)) (B C α : ℝ) (f : ℝ → ℝ)
    (hset : Setting Xs μ c) (hB : 0 ≤ B) (hH : HessBound Xs c B)
    (hopt : IsOptimal c μ πs) (hquant : Quant2 (X Xs) πs C α)
    (hα : 0 < α ∧ α ≤ 1) (hC : 0 < C) (hf : FStanding f) :
    ∀ n : ℕ, 1 ≤ n →
      ∃ πt π : Measure (E d), IsAtMostN n (X Xs) πt ∧ π ∈ couplings μ ∧
        (∫ x, c x ∂π) - (∫ x, c x ∂πs) ≤
          2 * B * C ^ 2 * (n : ℝ) ^ (-2 * α) ∧
        fDiv f π (prodRef μ) ≤ fDiv f πt (prodRef (marginal πt)) := by sorry

end RegOTQuant.TwiceDiff
