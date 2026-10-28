-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P12_lemmaB_2
-- name    : QAlgorithms.Papers.Independent.Claimed50.P12.lemmaB_2
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T18:50:26.767667+00:00
-- url     : https://prove2.me/theorems/b65eb37b-832d-44dd-8c18-f8f587797dac
-- title:
--   Relative entropy lower bounds normalized fidelity
-- statement:
--   Let $\rho,\sigma\ge0$ on a nonzero finite-dimensional system, with $\operatorname{tr}\rho>0$. For the normalized relative entropy in bits,
--
--   $$D(\rho\|\sigma)\ge-2\log_2\frac{F(\rho,\sigma)}{\operatorname{tr}\rho}.$$
--
--   The right side is $+\infty$ when the fidelity is zero. The positive first trace is the domain of the normalized relative entropy, and the trace denominator is retained even though the proof's Eq.160 drops it. This statement relates the two measures for arbitrary nonzero nonnegative inputs.
-- source:
--   Quantum conditional mutual information and approximate Markov chains, arXiv:1410.0664v3, PDF p. 21, Lemma B.2

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P12

noncomputable section

open Filter MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Claimed50.P12

open QAlgorithms.Papers.Independent.Information100.P32 (Op)

open QAlgorithms.Papers.Independent.Information100.P69 (CP matrixPower permute)

open QAlgorithms.Papers.Independent.Information100.P80 (OperatorLE groupedPower)

open QAlgorithms.Papers.Independent.Dependency50.P21 (marginalAB)

/-- Lemma B.2, Eq.157 (PDF p.21). Nonzero first input is the implicit domain
of Eq.16. Writing the logarithm as -log2 of the squared normalized fidelity
retains +infinity when the fidelity is zero. -/
theorem lemmaB_2 {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (rho sigma : Op I) (hrho : rho.PosSemidef) (hsigma : sigma.PosSemidef)
    (htrace : 0 < rho.trace.re) :
    negLogBits (ENNReal.ofReal ((rootFidelity rho sigma / rho.trace.re) ^ 2)) ≤
      normalizedRelativeEntropyBits rho sigma := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P12

end
