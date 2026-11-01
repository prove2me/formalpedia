-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P02_eveRenyi_eq7
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P02.eveRenyi_eq7
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T03:46:35.829158+00:00
-- url     : https://prove2.me/theorems/1956390e-f659-404e-bb86-45e367d3c462
-- title:
--   Optimal individual Rényi leakage for the split binary coherent signal
-- statement:
--   Let $n>0$ be the emitted mean photon number and let $0<\eta\le1$ be the intensity transmissivity. Use quadratures with $[x_1,x_2]=i/2$, so the coherent-state variance is $v=1/4$. Conditioned on the announced basis of the equiprobable four-state protocol, Eve holds one of the equally likely coherent states $|\pm\sqrt{(1-\eta)n}\rangle$.
--
--   For any single-pulse POVM $M$, let $P_+$ and $P_-$ be its two outcome laws and let $q=dP_+/d(P_++P_-)$. Its collision/Rényi information in bits is
--   $$
--   I^R(M)=\log_2\!\int\bigl(q(y)^2+(1-q(y))^2\bigr)\,d(P_++P_-)(y).
--   $$
--   The maximum over all POVMs, including arbitrary measurable outcome spaces, is attained and equals
--   $$
--   I^R_{\mathrm{opt}}(n,\eta)=\log_2\!\left(2-\exp\!\left[-\frac{(1-\eta)n}{v}\right]\right).
--   $$
--   The same POVM acts on both signs. It may be chosen after the basis announcement, and no collective measurement is allowed. The formal statement also establishes the coefficient realization and unit norms of the two coherent vectors.
--
--   This evaluates the individual leakage used in the paper's privacy-amplification gain. Eq.(6) is a cited background result; Eq.(7) is this paper's coherent-signal specialization.
-- source:
--   A practical limitation for continuous-variable quantum cryptography using coherent states, arXiv:quant-ph/0403115v1, PDF p. 2, Eq.(7)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P02

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P02

open MeasureTheory ProbabilityTheory

open scoped ENNReal Topology

open QAlgorithms.Papers.Independent.Dependency50.P39
  (Fock FockOperator coherentKet coherentCoefficient)

open QAlgorithms.Papers.Independent.Frontier30.P21 (coherentDensity)

open QAlgorithms.Papers.Independent.Next46.P32 (complexNormal quadrature)

open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity productCoeff)

/-- PDF p.2, (7): the optimal individual collision/Rényi leakage from the
binary split coherent signal, after learning the basis. -/
theorem eveRenyi_eq7 (n eta : ℝ) (hn : 0 < n) (heta : 0 < eta)
    (hetaOne : eta ≤ 1) :
    ReflectedPairRealized n eta ∧
    IsGreatest (leakageValues n eta)
      (Real.logb 2 (2 - Real.exp (-((1 - eta) * n) / (1 / 4 : ℝ)))) ∧
    optimalLeakage n eta =
      Real.logb 2 (2 - Real.exp (-((1 - eta) * n) / (1 / 4 : ℝ))) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P02

end
