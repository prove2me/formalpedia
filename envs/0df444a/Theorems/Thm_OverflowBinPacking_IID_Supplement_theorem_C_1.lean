-- Prove2me | Theorems.Thm_OverflowBinPacking_IID_Supplement_theorem_C_1
-- name    : OverflowBinPacking.IID.Supplement.theorem_C_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T05:01:15.07256+00:00
-- url     : https://prove2.me/theorems/c6d7e3fe-f964-4a04-877d-b2b6eca7fa6d
-- title:
--   Theorem C.1 — One threshold works at every horizon against one-active-bin policies
-- statement:
--   Let $\nu$ be any probability law with arbitrary finite support in $[0,\infty)$ and fix $C\ge1$. There is a single threshold $\alpha\in[0,1]$, chosen before the horizon, such that the corresponding policy is feasible and one-active-bin at every horizon, and
--   $$\forall n\ge0\ \forall a\text{ feasible and one-active-bin},\qquad \operatorname{cost}(\mathcal P_\alpha)\le\operatorname{cost}(a)+1.$$
--   The benchmark may know the horizon. The distribution may have zero-size mass or support above one. Retired bins cannot be reactivated, ties keep the current bin, and the same threshold must work for all horizons. This preserves the coefficient-one comparison and additive one of Appendix C.
--
--   Differences from the source:
--   - encoding: sequential policies and bins → the published zero-based Rule on Fin n, with measurable nonanticipative choices and strict overflow; reason: the immutable model is reused; measurability makes all expectations meaningful and changes no finite-support instance
--   - encoding: at most one bin active and permanently discarded bins → every bin label occurs in one contiguous interval of assignments on each outcome vector; reason: this is invariant under relabeling and permits any horizon-dependent feasible benchmark; the threshold is quantified before the horizon
-- source:
--   Perez-Salazar, Singh & Toriello, Adaptive Bin Packing with Overflow, arXiv:2007.11532v2, p. 44, Theorem C.1

import Mathlib
import Definitions.Def_OverflowBinPacking_IID_Supplement_Threshold

namespace OverflowBinPacking.IID.Supplement
open MeasureTheory

theorem theorem_C_1 (ν : Measure ℝ) (C : ℝ) (hC : 1 ≤ C)
    (hν : FiniteNonnegativeLaw ν) :
    ∃ α : ℝ, 0 ≤ α ∧ α ≤ 1 ∧ ∀ n : ℕ,
      IsPolicy (thresholdRule (n := n) α) ∧
      OneActive (thresholdRule (n := n) α) ∧
      ∀ a : Rule n, IsPolicy a → OneActive a →
        cost (fun _ => ν) C (thresholdRule (n := n) α) ≤ cost (fun _ => ν) C a + 1 := by sorry

end OverflowBinPacking.IID.Supplement
