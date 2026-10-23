-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P40_qubitLeadingAsymptotic
-- name    : QAlgorithms.Papers.Independent.Gap48.P40.qubitLeadingAsymptotic
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T05:29:33.844732+00:00
-- url     : https://prove2.me/theorems/5466b701-6f35-46f3-ab1e-89a9eda486c9
-- title:
--   §VII.A, unnumbered leading term in (48)
-- statement:
--   Fix $0<\beta\le1/2$ and denote the right-hand side of (46) by $B_2(\beta,T)=(T+1-\beta)\log((T+1-\beta)/(1-\beta))+(\beta-T)\log(1-T/\beta)$. Then
--
--   $$
--   \lim_{T\downarrow0}\frac{B_2(\beta,T)}{T^2}=\frac1{2\beta(1-\beta)}.
--   $$
--
--   This isolates the correct leading asymptotic from the defective printed series (48); it does not prescribe the leading coefficient of every relative entropy.
-- source:
--   Continuity bounds on the quantum relative entropy, arXiv:quant-ph/0503218v3, PDF p. 10, §VII.A, unnumbered leading term in (48)

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

/-- PDF p.10, Eq.(48), correct leading term only. The printed infinite series
is separately deferred; this asymptotic is of the bound (46), not of every entropy. -/
theorem qubitLeadingAsymptotic (beta : ℝ) (hbeta : 0 < beta ∧ beta ≤ 1 / 2) :
    Tendsto (fun T : ℝ => qubitSmallBound beta T / T ^ 2)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (1 / (2 * beta * (1 - beta)))) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P40

end
