-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P34_usual_log_truncation
-- name    : QAlgorithms.Papers.Independent.Extend50.P34.usual_log_truncation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:09:01.217354+00:00
-- url     : https://prove2.me/theorems/f544d815-1de4-490f-9e3f-fae9d3014d47
-- title:
--   Lemma 5.3
-- statement:
--   Under $n=r^2/\omega^2$, $200\le\omega\le\sqrt r$, let $\lambda\vdash n$ be usual. Define $L_C=\sum_{k=2}^C(-1)^kp_k^*/(kr^k)$ and $L_\infty^*=\sum_{k\ge2}(-1)^kp_k^*/[k(r+1/2)^k]$. If $C\ge3\log(10r)/\log(\omega/10)$, the infinite series is absolutely convergent and
--
--   $$|L_\infty^*(\lambda)-L_C(\lambda)|\le201/\omega^3.$$
--
--   The bound covers both truncation and replacement of $r+1/2$ by $r$. This justifies using the finite observable on usual diagrams.
-- source:
--   Quantum Spectrum Testing, arXiv:1501.05028v1, PDF p. 46, Lemma 5.3

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P34

noncomputable section

open scoped Matrix BigOperators

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P34

attribute [local instance] Classical.propDecidable

-- Reuse exact pinned definitions; these are imports, not local declarations.

open QAlgorithms.Papers.Independent.Support50.P38 (tv wordMass)

open QAlgorithms.Papers.Independent.Advance50.P28 (counts)

/-- Lemma 5.3, arXiv:1501.05028v1, PDF p.46. Summability excludes the default tsum value on divergent input. Usual event and omega≤sqrt(r) are retained. -/
theorem usual_log_truncation
    (r n C : ℕ) (omega : ℝ) (hregime : RankRegime r n omega)
    (lambda : YoungDiagram) (hsize : lambda.card = n) (husual : Usual r omega lambda)
    (hC : 3*Real.log (10*r)/Real.log (omega/10) ≤ (C : ℝ)) :
    Summable (fun k : ℕ => if 2 ≤ k then
      (-1 : ℝ)^k * starPower k lambda / ((k : ℝ)*((r : ℝ)+1/2)^k) else 0) ∧
    |logInfinite r lambda - logObservable r C lambda| ≤ 201/omega^3 := by sorry

end QAlgorithms.Papers.Independent.Extend50.P34

end
