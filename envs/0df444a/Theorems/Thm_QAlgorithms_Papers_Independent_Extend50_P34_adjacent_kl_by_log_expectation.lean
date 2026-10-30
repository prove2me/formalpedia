-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P34_adjacent_kl_by_log_expectation
-- name    : QAlgorithms.Papers.Independent.Extend50.P34.adjacent_kl_by_log_expectation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:09:35.250982+00:00
-- url     : https://prove2.me/theorems/c78e12ba-4c1c-441f-b0e0-a3a843999b03
-- title:
--   Proposition 5.4
-- statement:
--   Suppose $r,n\ge1$, $n=r^2/\omega^2$, $200\le\omega\le\sqrt r$, and
--
--   $$\frac{3\log(10r)}{\log(\omega/10)}\le C\le\frac{3r}{\omega\log r}.$$
--
--   Then $D_{\rm KL}(\mathrm{SW}_r^n\|\mathrm{SW}_{r+1}^n)\le\mathbb E_{\mathrm{SW}_r^n}L_C+203/\omega^3$, where $L_C=\sum_{k=2}^C(-1)^kp_k^*/(kr^k)$. The expectation is signed. This reduces the divergence bound to a finite observable expectation.
-- source:
--   Quantum Spectrum Testing, arXiv:1501.05028v1, PDF p. 47, Proposition 5.4

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P34

noncomputable section

open scoped Matrix BigOperators

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P34

attribute [local instance] Classical.propDecidable

-- Reuse exact pinned definitions; these are imports, not local declarations.

open QAlgorithms.Papers.Independent.Support50.P38 (tv wordMass)

open QAlgorithms.Papers.Independent.Advance50.P28 (counts)

/-- Proposition 5.4, arXiv:1501.05028v1, PDF p.47. Upper truncation limit is 3r/(omega log r). KL direction is r to r+1; its support inclusion makes it finite. -/
theorem adjacent_kl_by_log_expectation
    (r n C : ℕ) (omega : ℝ) (hregime : RankRegime r n omega)
    (hClo : 3*Real.log (10*r)/Real.log (omega/10) ≤ (C : ℝ))
    (hChi : (C : ℝ) ≤ 3*r/(omega*Real.log r)) :
    adjacentKL r n ≤ expect (n := n) (unif r) (logObservable r C) + 203/omega^3 := by sorry

end QAlgorithms.Papers.Independent.Extend50.P34

end
