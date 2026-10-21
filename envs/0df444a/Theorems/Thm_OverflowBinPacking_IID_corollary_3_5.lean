-- Prove2me | Theorems.Thm_OverflowBinPacking_IID_corollary_3_5
-- name    : OverflowBinPacking.IID.corollary_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:31:32.039983+00:00
-- url     : https://prove2.me/theorems/d7f6ce03-4bfb-4382-9e62-e26fd948f40d
-- title:
--   Corollary 3.5, p. 10 — Budgeted Greedy cost bounded by expected bin openings
-- statement:
--   Under the assumptions of Lemma 3.4, Budgeted Greedy's opening and overflow costs satisfy
--   $$\operatorname{cost}(\mathrm{BG})\le(1+\gamma)\,\mathbb E[N_{\mathrm{BG}}].$$
--   Here $N_{\mathrm{BG}}$ is the number of bins it opens. The bound turns later comparisons of expected bin openings into comparisons of total cost.
--
--   **Formalization Note** The independent nonnegative item laws, $C\ge1$, $\gamma\ge1$, and $\Pr(X_i>1)\le\gamma/C$ are explicit binders.
-- source:
--   Perez-Salazar, Singh & Toriello, Adaptive Bin Packing with Overflow, arXiv:2007.11532v2, p. 10, Corollary 3.5

import Mathlib
import Definitions.Def_OverflowBinPacking_IID_BudgetedGreedy

namespace OverflowBinPacking.IID

open MeasureTheory

/-- Corollary 3.5, p. 10: risk budgeting controls expected overflow cost. -/
theorem corollary_3_5 {n : ℕ} (μ : Fin n → Measure ℝ)
    (hμ : ∀ i, IsProbabilityMeasure (μ i))
    (hμ0 : ∀ i, μ i (Set.Iio 0) = 0)
    (C γ : ℝ) (hC : 1 ≤ C) (hγ : 1 ≤ γ)
    (hLight : ∀ i, (μ i).real (Set.Ioi 1) ≤ γ / C) :
    cost μ C (bgRule μ C γ) ≤
      (1 + γ) * ∫ x, (numOpened (bgRule μ C γ) x : ℝ) ∂(Measure.pi μ) := by sorry

end OverflowBinPacking.IID
