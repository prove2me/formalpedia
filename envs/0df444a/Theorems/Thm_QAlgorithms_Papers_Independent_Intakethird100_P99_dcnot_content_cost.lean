-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P99_dcnot_content_cost
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P99.dcnot_content_cost
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T10:10:22.03057+00:00
-- url     : https://prove2.me/theorems/9ca0a129-30fd-4904-8b41-dbf4e83b0e5a
-- title:
--   DCNOT interaction content and cost
-- statement:
--   Let $H$ be a Hermitian Hamiltonian on two qubits $A,B$, with canonical interaction coefficients $\alpha=(\alpha_1,\alpha_2,\alpha_3)$ satisfying $\alpha_1\ge\alpha_2\ge|\alpha_3|$. Local terms in $H$ are allowed. Local unitary controls are instantaneous and free, interaction intervals are nonnegative, and $\hbar=1$. Write $C_H(U)$ for the infimum of the interaction durations of protocols implementing the gate $U$, allowing the ideal limit of arbitrarily fine pulses at fixed total duration and disregarding global phase. This cost is an extended nonnegative real, with value $+\infty$ for an impossible simulation. Assume $\alpha_1>0$. Define $\mathrm{DCNOT}:|i,j\rangle\mapsto|j,i\oplus j\rangle$, where $i,j\in\{0,1\}$ and $\oplus$ is addition modulo two. Its canonical interaction content and cost are
--
--   $$\beta(\mathrm{DCNOT})=\frac{\pi}{4}(1,1,0),\qquad C_H(\mathrm{DCNOT})=\frac{\pi}{2(\alpha_1+\alpha_2-|\alpha_3|)}.$$
--
--   The explicit basis action fixes the order of the two controlled-NOT operations.
-- source:
--   Characterization of non-local gates, arXiv:quant-ph/0205100v3, PDF p. 7, III.D.2: DCNOT content and interaction cost

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P99

namespace QAlgorithms.Papers.Independent.Intakethird100.P99

open scoped Matrix Kronecker NNReal ENNReal

open QAlgorithms.Papers.Independent.Information100.P10 (pauli)

open QAlgorithms.Papers.Independent.Information100.P32 (evolution)

noncomputable section

/-- PDF p.7, III.D.2: DCNOT's basis action fixes the product convention; the cost
has denominator a1+a2-|a3| and numerator pi/2. -/
theorem dcnot_content_cost (H : TwoMatrix) (a : Triple)
    (hH : HasCanonicalHamiltonian H a) (ha : 0 < a 0) :
    HasContent dcnot ![Real.pi / 4, Real.pi / 4, 0] ∧
      interactionCost H dcnot =
        ENNReal.ofReal (Real.pi / (2 * (a 0 + a 1 - |a 2|))) := by sorry

end

end QAlgorithms.Papers.Independent.Intakethird100.P99
