-- Prove2me | Theorems.Thm_PipelineInterv_Welfare_lemma_1
-- name    : PipelineInterv.Welfare.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:23:08.141965+00:00
-- url     : https://prove2.me/theorems/059d71e7-636d-4938-b58b-7351f0a7a21b
-- title:
--   Lemma 1, p. 11 — a left stochastic matrix is non-expansive in ℓ1 on distributions
-- statement:
--   Let $M\in\mathbb R^{w\times w}$ be a left stochastic matrix (nonnegative entries, every column summing to one) and let $D,D'\in\mathcal D$ be probability distributions on $[w]$. Then
--   $$\|MD-MD'\|_1\le\|D-D'\|_1 .$$
--
--   Applying a transition matrix cannot increase the $\ell_1$ distance between two distributions. This is what lets the dynamic program track distributions on a finite net with an error that does not grow from one layer to the next.
--
--   **Formalization Note.** $\|x\|_1$ is written out as $\sum_i|x_i|$.
-- source:
--   Arunachaleswaran, Kannan, Roth, Ziani, Pipeline Interventions, arXiv:2002.06592v2, p. 11, Lemma 1

import Mathlib
import Definitions.Def_PipelineInterv_Welfare_Model

namespace PipelineInterv.Welfare
open Matrix

theorem lemma_1 {w : ℕ} (M : Matrix (Fin w) (Fin w) ℝ) (hM : M ∈ colStochastic ℝ (Fin w))
    (D D' : Fin w → ℝ) (hD : IsDist D) (hD' : IsDist D') :
    l1 (M *ᵥ D - M *ᵥ D') ≤ l1 (D - D') := by sorry

end PipelineInterv.Welfare
