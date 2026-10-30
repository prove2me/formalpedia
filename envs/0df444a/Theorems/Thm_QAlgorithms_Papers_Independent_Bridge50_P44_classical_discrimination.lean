-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P44_classical_discrimination
-- name    : QAlgorithms.Papers.Independent.Bridge50.P44.classical_discrimination
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:11:29.156355+00:00
-- url     : https://prove2.me/theorems/167537c4-1bd1-447e-b114-881e5cd6955c
-- title:
--   A.2: classical discrimination identity
-- statement:
--   Let $P,Q$ be normalized discrete laws on one alphabet. A single sample is drawn from one of them, with prior probability $1/2$ each. Optimizing over all decision rules, including randomized rules, gives
--
--   $$p_{\mathrm{distinguish}}(P,Q)=\tfrac12+\tfrac12D(P,Q).$$
--
--   The optimum is attained. All sums are absolutely convergent. This is a one-sample, equal-prior operational interpretation of total variation.
-- source:
--   Cryptographic security of quantum key distribution, arXiv:1409.3525v1, PDF p. 39, A.2: classical discrimination identity

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P44

noncomputable section

open scoped BigOperators Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Bridge50.P44

open QAlgorithms

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33 (State traceSize)

open QAlgorithms.Papers.Independent.Dependency50.P24 (cqState)

open QAlgorithms.Papers.Independent.Frontier18.P08 (partialTraceFirst)

open QAlgorithms.Papers.Independent.Information100.P76 (maximallyMixed)

open QAlgorithms.Papers.Independent.Frontier18.P08 (conditionalEntropyNats)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- PDF pp.38--39, Appendix A.2: optimal classical one-sample discrimination,
with equal priors and unrestricted randomized rules. A rule attains the optimum. -/
theorem classical_discrimination {Z : Type*} (p q : Z → ℝ)
    (hp : IsDiscreteLaw p) (hq : IsDiscreteLaw q) :
    optimalBinaryTestSuccess p q = 1 / 2 + (1 / 2 : ℝ) * discreteTV p q ∧
    ∃ g, binaryTestSuccess p q g = optimalBinaryTestSuccess p q := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P44

end
