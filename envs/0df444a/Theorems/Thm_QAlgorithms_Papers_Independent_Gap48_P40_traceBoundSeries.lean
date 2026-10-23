-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P40_traceBoundSeries
-- name    : QAlgorithms.Papers.Independent.Gap48.P40.traceBoundSeries
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T05:32:48.574985+00:00
-- url     : https://prove2.me/theorems/d360fbfd-4cee-4843-aa1c-57066f21a5c8
-- title:
--   §VII.B, unnumbered series and leading term (57)
-- statement:
--   Fix $\beta>0$ and define $B_1(\beta,T)=(\beta+T)\log((\beta+T)/\beta)+(\beta-T)\log((\beta-T)/\beta)$. For $0\le T<\beta$,
--
--   $$
--   B_1(\beta,T)=\sum_{k=1}^{\infty}\frac{T^{2k}}{k(2k-1)\beta^{2k-1}},\qquad\lim_{T\downarrow0}\frac{B_1(\beta,T)}{T^2}=\frac1\beta.
--   $$
--
--   The convergent series and leading coefficient belong to bound (55), rather than to every state pair.
-- source:
--   Continuity bounds on the quantum relative entropy, arXiv:quant-ph/0503218v3, PDF p. 12, §VII.B, unnumbered series and leading term (57)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P40

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Topology Matrix.Norms.L2Operator

open Filter MeasureTheory Asymptotics

open QAlgorithms

open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy)

open QAlgorithms.Papers.Independent.Information100.P50 (IsUINorm)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P60 (copies)

open QAlgorithms.Papers.Independent.Information100.P44 (Mat)

namespace QAlgorithms.Papers.Independent.Gap48.P40

/-- PDF p.12, Eq.(57): convergent series for (55) on 0<=T<beta and its
leading term. Index k+1 avoids truncated subtraction in exponents and denominators. -/
theorem traceBoundSeries (beta : ℝ) (hbeta : 0 < beta) :
    (∀ T : ℝ, 0 ≤ T → T < beta →
      HasSum (fun k : ℕ => T ^ (2 * (k + 1)) /
        (((k + 1 : ℕ) : ℝ) * (2 * ((k + 1 : ℕ) : ℝ) - 1) * beta ^ (2 * k + 1)))
        (traceSmallBound beta T)) ∧
    Tendsto (fun T : ℝ => traceSmallBound beta T / T ^ 2)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (1 / beta)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P40

end
