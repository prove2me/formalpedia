-- Prove2me | Theorems.Thm_TalagrandCore_sigma2_weighted_exp
-- name    : TalagrandCore.sigma2_weighted_exp
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-13T04:59:00.776632+00:00
-- url     : https://prove2.me/theorems/d02aabd2-20ff-48d1-8843-a695cc38b6e4
-- title:
--   Weighted exponential moment bound for a nonnegative supremum process
-- statement:
--   For a finite supremum process $Y$ with summands in $[0,1]$,
--
--   $$
--   \mathbb E\!\left[Y e^{Y/8}\right]
--   \le 24\,\mathbb E[Y]\exp\!\left(\frac34\mathbb E[Y]\right).
--   $$
--
--   This weighted self-bounding estimate is used to control the random variance process in the Gaussian upper-tail regime.
--
--   **Formalization Note** The constants are the explicit constants used by the accepted finite-Boolean proof.
-- source:
--   Michel Ledoux, On Talagrand’s deviation inequalities for product measures, ESAIM Probability and Statistics 1 (1996), Theorems 2.4–2.5, pp. 63–87. Formal Lean proof extracted from Prove2Me accepted submission bf106d23-ff42-48f5-a837-a8528101c849 by tianyipeng.

import Definitions.Def_talagrand_finite_bool_core
open MeasureTheory
open scoped Classical BigOperators

namespace TalagrandCore

variable {κ ι : Type} [DecidableEq κ] [Fintype κ]
variable [Fintype ι] [Nonempty ι]

theorem sigma2_weighted_exp (p : NNReal) (hp : p ≤ 1)
    (g : ι → κ → Bool → ℝ) (hg0 : ∀ a x b, 0 ≤ g a x b) (hg1 : ∀ a x b, g a x b ≤ 1) :
    Ex (p : ℝ) (fun ω => supProc g ω * Real.exp (supProc g ω / 8)) ≤
      24 * Ex (p : ℝ) (fun ω => supProc g ω) *
        Real.exp (3 / 4 * Ex (p : ℝ) (fun ω => supProc g ω)) := by sorry

end TalagrandCore
