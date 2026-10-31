-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P28_typicality_exponent
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P28.typicality_exponent
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:53:31.348606+00:00
-- url     : https://prove2.me/theorems/143debf4-c42f-47aa-8a8b-fadc7ae6c68e
-- title:
--   Theorem 30: Strong-typicality exponent bounds: phi_balance(1-betaQ)Qmin^2 delta^2<=L_delta(Q)<=log(1+2Qmin delta^2); upper bound only when delta<(1-Qmax)/Qmin
-- statement:
--   Let $Q$ be a strictly positive law on a finite alphabet of size greater than 1, and $\delta>0$. Let $L_\delta(Q)$ be the extended infimum of $D(P\|Q)$ over laws outside the closed relative-coordinate ball $|P(i)-Q(i)|\le\delta Q(i)$. Let $\beta_Q=\inf\{Q(F):Q(F)\ge1/2\}$ and $\varphi(p)=\log_b((1-p)/p)/[4(1-2p)]$ for $0<p<1/2$, with $\varphi(1/2)=(\log_b e)/2$. Then
--
--   $$\varphi(1-\beta_Q)Q_{\min}^2\delta^2\le L_\delta(Q),$$
--
--   and $L_\delta(Q)\le\log_b(1+2Q_{\min}\delta^2)$ if $\delta<(1-Q_{\max})/Q_{\min}$. The empty complement has exponent infinity. The printed minimum in (388) is read as an infimum, as required by the limiting proof (396).
-- source:
--   $f$-divergence Inequalities, arXiv:1508.00335v7, PDF p. 56, Theorem 30

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P28

noncomputable section

open MeasureTheory Set Filter

open scoped ENNReal NNReal Topology BigOperators ProbabilityTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P28

universe u

attribute [local instance] Classical.propDecidable

/-- Theorem 30: Strong-typicality exponent bounds: phi_balance(1-betaQ)Qmin^2 delta^2<=L_delta(Q)<=log(1+2Qmin delta^2); upper bound only when delta<(1-Qmax)/Qmin. Sason--Verdu, arXiv:1508.00335v7, PDF p.56. Source correction: (388) prints min over an open complement; use infimum with +infinity for empty complement. No theorem parameter domain is restricted. -/
theorem typicality_exponent
    (b : LogBase) (n : ℕ) (hn : 1 < n) (q : Fin n → ℝ)
    (hq : FiniteProbabilityLaw q) (hqpos : ∀ i, 0 < q i) (d : ℝ) (hd : 0 < d) :
    ENNReal.ofReal (balancePhi b (1 - balance q) * minReferenceMass q ^ 2 * d ^ 2) ≤ typicalExponent b q d ∧
    (d < (1 - qMax q) / minReferenceMass q →
      typicalExponent b q d ≤ ENNReal.ofReal (logB b (1 + 2 * minReferenceMass q * d ^ 2))) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P28

end
