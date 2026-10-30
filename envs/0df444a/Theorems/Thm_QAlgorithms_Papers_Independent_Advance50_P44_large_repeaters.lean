-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P44_large_repeaters
-- name    : QAlgorithms.Papers.Independent.Advance50.P44.large_repeaters
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T09:15:32.350007+00:00
-- url     : https://prove2.me/theorems/0a04a74e-1a88-4abb-87db-2d40dc5b8541
-- title:
--   Repeater-dominant additive asymptotic
-- statement:
--   Fix a total transmissivity $0<\eta<1$. For each nonnegative integer $N$, let
--   $$F(\eta,N)=-\log_2\!\left(1-\eta^{1/(N+1)}\right),$$
--   the explicit equal-spacing rate expression in Eq. (113), measured in bits per chain use. As the number of repeaters tends to infinity,
--   $$\lim_{N\to\infty}\left[F(\eta,N)-\left(\log_2 N-\log_2\ln(1/\eta)\right)\right]=0.$$
--   Thus the logarithmic coefficient is independent of the fixed loss; the additive offset depends on that loss.
--
--   **Formalization Note** This node is the analytic expansion of the explicit expression. The separate operational capacity identification and placement optimization are deferred; neither is a hypothesis of this limit theorem.
-- source:
--   End-to-end capacities of a quantum communication network, arXiv:1905.12674v1, PDF p. 19, Unnumbered repeater-dominant asymptotic, Eq. (114)

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P44

namespace QAlgorithms.Papers.Independent.Advance50.P44

noncomputable section

open Filter

/-- PDF p.19, Eq.(114): for fixed total transmissivity in (0,1), the
equal-spacing expression has the stated additive logarithmic expansion.
The offset depends on eta. The totalized log at N=0 affects only a finite
prefix of the sequence and imposes no restriction on the number of repeaters. -/
theorem large_repeaters (eta : ℝ) (heta0 : 0 < eta) (heta1 : eta < 1) :
    Tendsto (fun N : ℕ => equalSpacingLossExpression eta N -
      (Real.logb 2 (N : ℝ) - Real.logb 2 (Real.log (1 / eta))))
      atTop (nhds 0) := by sorry

end

end QAlgorithms.Papers.Independent.Advance50.P44
