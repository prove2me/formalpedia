-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P34_unusual_probability
-- name    : QAlgorithms.Papers.Independent.Extend50.P34.unusual_probability
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:08:08.763067+00:00
-- url     : https://prove2.me/theorems/1a5c80fa-03c5-4c1a-be21-dc2ccd0f4559
-- title:
--   Lemma 5.2
-- statement:
--   Let $r,n$ be positive integers and $200\le\omega\le\sqrt r$, with $n=r^2/\omega^2$. A diagram is usual when both its width and height are at most $10r/\omega$. Then
--
--   $$\Pr_{\lambda\sim\mathrm{SW}_r^n}[\lambda\text{ unusual}]\le2^{-20r/\omega}.$$
--
--   The width and height predicates use real thresholds without rounding. This controls the event on which the logarithmic expansion may fail.
-- source:
--   Quantum Spectrum Testing, arXiv:1501.05028v1, PDF p. 46, Lemma 5.2

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P34

noncomputable section

open scoped Matrix BigOperators

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P34

attribute [local instance] Classical.propDecidable

-- Reuse exact pinned definitions; these are imports, not local declarations.

open QAlgorithms.Papers.Independent.Support50.P38 (tv wordMass)

open QAlgorithms.Papers.Independent.Advance50.P28 (counts)

/-- Lemma 5.2, arXiv:1501.05028v1, PDF p.46.  -/
theorem unusual_probability
    (r n : ℕ) (omega : ℝ) (hregime : RankRegime r n omega) :
    event (n := n) (unif r) (fun lambda => ¬ Usual r omega lambda) ≤
      Real.rpow 2 (-20*r/omega) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P34

end
