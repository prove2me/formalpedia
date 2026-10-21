-- Prove2me | Theorems.Thm_OverflowBinPacking_IID_lemma_4_3
-- name    : OverflowBinPacking.IID.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:31:38.402725+00:00
-- url     : https://prove2.me/theorems/970d5c4a-aeaf-472e-87ac-3c8964bdb50d
-- title:
--   Lemma 4.3, p. 13 — Budgeted Greedy minimizes expected bin openings
-- statement:
--   Suppose $X_1,\ldots,X_n$ are nonnegative i.i.d. items, $C\ge1$, $\gamma\ge1$, and $\Pr(X_1>1)\le\gamma/C$. Budgeted Greedy itself respects the risk budget $\gamma/C$. Among every measurable feasible policy $P$ respecting that budget, it minimizes the expected number of opened bins:
--   $$\mathbb E[N_{\mathrm{BG}}]\le\mathbb E[N_P].$$
--   This is the i.i.d. exchange result used in Theorem 4.4.
--
--   **Formalization Note** The light-item condition is added to the printed lemma. Without it, a bin holding even one item can exceed the stated risk budget, and the assertion that Budgeted Greedy is budgeted fails. The proof of Theorem 4.4 invokes this lemma only in the light-item case.
-- source:
--   Perez-Salazar, Singh & Toriello, Adaptive Bin Packing with Overflow, arXiv:2007.11532v2, p. 13, Lemma 4.3; p. 14, proof of Theorem 4.4

import Mathlib
import Definitions.Def_OverflowBinPacking_IID_BudgetedGreedy

namespace OverflowBinPacking.IID

open MeasureTheory

/-- Lemma 4.3, p. 13: among policies respecting the budget,
Budgeted Greedy opens the fewest bins in expectation. -/
theorem lemma_4_3 {n : ℕ} (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν0 : ν (Set.Iio 0) = 0)
    (C γ : ℝ) (hC : 1 ≤ C) (hγ : 1 ≤ γ)
    (hLight : ν.real (Set.Ioi 1) ≤ γ / C) :
    IsBudgeted (fun _ : Fin n => ν) (bgRule (fun _ : Fin n => ν) C γ) (γ / C) ∧
    ∀ a : Rule n, IsPolicy a → IsBudgeted (fun _ : Fin n => ν) a (γ / C) →
      (∫ x, (numOpened (bgRule (fun _ : Fin n => ν) C γ) x : ℝ)
        ∂(Measure.pi (fun _ : Fin n => ν))) ≤
      (∫ x, (numOpened a x : ℝ) ∂(Measure.pi (fun _ : Fin n => ν))) := by sorry

end OverflowBinPacking.IID
