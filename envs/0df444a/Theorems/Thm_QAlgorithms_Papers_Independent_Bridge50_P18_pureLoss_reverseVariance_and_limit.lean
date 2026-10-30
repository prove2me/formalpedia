-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P18_pureLoss_reverseVariance_and_limit
-- name    : QAlgorithms.Papers.Independent.Bridge50.P18.pureLoss_reverseVariance_and_limit
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:53:41.606039+00:00
-- url     : https://prove2.me/theorems/80049b3f-e865-483b-a6e5-46bc353f786c
-- title:
--   Pure-loss reverse coherent-information variance and its zero high-energy limit
-- statement:
--   Fix an intensity transmissivity $0<\eta<1$. For $S>0$, prepare the normalized two-mode squeezed vacuum with mean signal photon number $S$, send its second mode through the vacuum pure-loss channel of transmissivity $\eta$, and denote the actual output by $\rho_{AB}(\eta,S)$, with $A$ the untouched reference. Put $q=1-\eta$. In bits squared, the reverse coherent-information variance, equivalently the conditional entropy variance $V(B|A)$, is
--
--   $$
--   \begin{aligned}
--   V(B|A)_{\rho(\eta,S)}={}&qS(qS+1)\left[\log_2\left(1+\frac1{qS}\right)\right]^2\\
--   &-2qS(S+1)\log_2\left(1+\frac1{qS}\right)\log_2\left(1+\frac1S\right)\\
--   &+S(S+1)\left[\log_2\left(1+\frac1S\right)\right]^2.
--   \end{aligned}
--   $$
--
--   For each fixed $\eta$, the independently defined conditional variance obeys
--
--   $$
--   \lim_{S\to+\infty}V(B|A)_{\rho(\eta,S)}=0.
--   $$
--
--   Here conditional variance is the centered second moment of $\log_2\rho_{AB}-\log_2(\rho_A\otimes I_B)$, interpreted on the support of $\rho_{AB}$. This calculation does not establish the conjectural infinite-dimensional key-achievability statements (A8)–(A9).
--
--   **Formalization Note** The output is constructed by the squeezed-vacuum and vacuum-loss purification coefficients followed by the environment partial trace. The theorem includes density normalization, bounded realizations, and convergence of bounded-log centered moments to their defined conditional variance. The approximate square (A43) is not asserted as an identity.
-- source:
--   Upper bounds on secret key agreement over lossy thermal bosonic channels, arXiv:1706.04590v2, PDF p. 11, Appendix A, (A10)–(A42), limit after (A43)

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P18

noncomputable section

open Filter

open scoped BigOperators ENNReal Topology

namespace QAlgorithms.Papers.Independent.Bridge50.P18

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsDensity)

open QAlgorithms.Papers.Independent.Dependency50.P13 (operatorTrace)

open QAlgorithms.Papers.Independent.Information100.P63 (logTwo tensorPower)

open QAlgorithms.Papers.Independent.Support50.P20 (hilbertTestingDivergence)

open QAlgorithms.Papers.Independent.Claimed50.P19
  (Cov GaussianWithCovariance multimodeWeylTrace covarianceCharacteristicValue)

-- The accepted complete coordinate basis has the identical body and type.

open QAlgorithms.Papers.Independent.Next46.P13 (coordinateBasis)

/-- PDF pp.9--11, Appendix A, (A10)--(A42) and the limit after (A43).
Both the exact independently defined conditional variance and its actual
high-energy Tendsto are retained. S>0 excludes reciprocals at vacuum; eta is
fixed in (0,1). Normalization and the bounded operator realizations are included
to pin the physical output and prevent any off-domain realization fallback.
This does not assert the conjectural capacity/achievability bounds (A8),(A9). -/
theorem pureLoss_reverseVariance_and_limit (eta : ℝ)
    (heta0 : 0 < eta) (heta1 : eta < 1) :
    (∀ S : ℝ, 0 < S →
      IsDensity (pureLossOutput eta S) ∧
      HasCoefficients (realizeCoefficients (pureLossOutput eta S)) (pureLossOutput eta S) ∧
      HasCoefficients (realizeCoefficients (reverseReference S)) (reverseReference S) ∧
      Tendsto (conditionalVarianceCutoff (pureLossOutput eta S) (reverseReference S))
        atTop (nhds (conditionalVarianceBits (pureLossOutput eta S) (reverseReference S))) ∧
      conditionalVarianceBits (pureLossOutput eta S) (reverseReference S) =
        pureLossVarianceExpression eta S) ∧
    Tendsto (fun S : ℝ => conditionalVarianceBits (pureLossOutput eta S) (reverseReference S))
      atTop (nhds 0) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P18

end
