-- Prove2me | Theorems.Thm_SampleCRS_AlmostGreedy_Supplement_theorem_b_2
-- name    : SampleCRS.AlmostGreedy.Supplement.theorem_b_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:43:20.629068+00:00
-- url     : https://prove2.me/theorems/b52e8af3-f3ce-4a1f-84e6-502c629eba38
-- title:
--   Theorem B.2 — the full second-difference expectation expansion
-- statement:
--   Let $X,Y$ have arbitrary laws on $\mathbb N$ with finite means. Define $\delta=E[X]-E[Y]$ and $D_j=E[(X-j-1)^+]-E[(Y-j-1)^+]$. For any $f:\mathbb N\to\mathbb R$ satisfying
--   $$\sum_{j\ge0}\bigl(E[(X-j-1)^+]+E[(Y-j-1)^+]\bigr)|\Delta^2f(j)|<\infty,$$
--   the expectations of $f(X),f(Y)$ are finite, the signed expansion is summable, and
--   $$E[f(X)]-E[f(Y)]=\delta\Delta f(0)+\sum_{j\ge0}D_j\Delta^2f(j).$$
--   The means need not be equal. Neither independence nor common underlying probability space, bounded support, extra moments or convexity is assumed. The integrability and convergence conclusions make the displayed equality an equality of genuine finite expectations and convergent series.
--
--   Differences from the source:
--   - encoding: arbitrary N-supported random variables with finite means → their probability laws NatLaw on N with integrable first moment; reason: every such random variable has this pushforward law, and every such law is realized by the identity variable
--   - encoding: the printed absolute summability hypothesis and expectation-series equality → Summable of the nonnegative weighted absolute differences, with integrability and signed summability asserted in the conclusion; reason: these are exactly the well-definedness consequences implicit in the source equality; they prevent totalized real integrals or tsum from assigning a spurious zero
-- source:
--   Shaddin Dughmi, Vasilis Livanos, Pranav Nuti, STOC 2027 submission #686 (October 2026), Theorem B.2, p. 38

import Mathlib
import Definitions.Def_SampleCRS_AlmostGreedy_Supplement_discreteOrder

namespace SampleCRS.AlmostGreedy.Supplement

/-- Theorem B.2, p.38. the full second-difference expectation expansion. -/
theorem theorem_b_2 (P Q : NatLaw) (f : ℕ → ℝ) (hs : SecondDifferenceSummable P Q f) :
    MeasureTheory.Integrable f P.law ∧ MeasureTheory.Integrable f Q.law ∧
    Summable (fun j => stopDifference P Q j * delta2 f j) ∧
    (∫ j, f j ∂P.law) - (∫ j, f j ∂Q.law) =
      (mean P - mean Q) * delta f 0 + ∑' j, stopDifference P Q j * delta2 f j := by sorry

end SampleCRS.AlmostGreedy.Supplement
