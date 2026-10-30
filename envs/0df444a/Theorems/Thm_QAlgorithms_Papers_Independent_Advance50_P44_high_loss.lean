-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P44_high_loss
-- name    : QAlgorithms.Papers.Independent.Advance50.P44.high_loss
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T09:16:06.066913+00:00
-- url     : https://prove2.me/theorems/fc53f889-d3c8-43e7-9e56-bfea832e6cac
-- title:
--   Fixed-repeater high-loss asymptotic
-- statement:
--   Fix a nonnegative integer $N$. Write $F(\eta,N)=-\log_2(1-\eta^{1/(N+1)})$ for the equal-spacing rate expression in Eq. (113), in bits per chain use. Then
--   $$\lim_{\eta\downarrow0}\frac{F(\eta,N)}{\eta^{1/(N+1)}/\ln2}=1.$$
--   The number of repeaters is fixed throughout this limit. Multiplication by $\ln2$ converts bits to nats, giving leading term $\eta^{1/(N+1)}$ nats per use. The printed coefficient $1.44$ is a decimal approximation to $1/\ln2$.
--
--   **Formalization Note** The one-sided filter excludes zero and is eventually contained in $(0,1)$. This states the analytic asymptotic of Eq. (113); the operational identification of that expression is separately deferred.
-- source:
--   End-to-end capacities of a quantum communication network, arXiv:1905.12674v1, PDF p. 19, Unnumbered loss-dominant asymptotic, Eq. (115)

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P44

namespace QAlgorithms.Papers.Independent.Advance50.P44

noncomputable section

open Filter

/-- PDF p.19, Eq.(115): at fixed N, the high-loss expression is asymptotic
to eta^(1/(N+1))/ln 2 bits per use. The printed 1.44 is rounded.
The right-hand limit stays eventually in the physical interval (0,1);
eta=0 is excluded by the filter, so division by a zero leading term is unused. -/
theorem high_loss (N : ℕ) :
    Tendsto (fun eta : ℝ => equalSpacingLossExpression eta N /
      (eta ^ (1 / ((N : ℝ) + 1)) / Real.log 2))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by sorry

end

end QAlgorithms.Papers.Independent.Advance50.P44
