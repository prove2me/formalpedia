-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P49_operational_fidelity_equivalence
-- name    : QAlgorithms.Papers.Independent.Dependency50.P49.operational_fidelity_equivalence
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T18:18:33.391445+00:00
-- url     : https://prove2.me/theorems/f9611112-4dfd-461b-b165-a57b822546fc
-- title:
--   Operational fidelity and cb-distance
-- statement:
--   Let $T_1,T_2:\mathcal B(H_B)\to\mathcal B(H_A)$ be completely positive unital complex-linear maps between positive-dimensional finite complex systems, and let $T_{i*}$ denote their trace-dual channels. For density operators, write $f(\rho,\sigma)=\operatorname{tr}\sqrt{\sqrt\rho\,\sigma\sqrt\rho}$ for root fidelity. Define
--
--   $$F(T_1,T_2)=\inf_{\rho\text{ density on }H_A\otimes H_A}f((\operatorname{id}_A\otimes T_{1*})(\rho),(\operatorname{id}_A\otimes T_{2*})(\rho)).$$
--
--   Then
--
--   $$1-F(T_1,T_2)\leq\tfrac12\|T_1-T_2\|_{\rm cb}\leq\sqrt{1-F(T_1,T_2)^2}.$$
--
--   The cb-norm is unhalved. This compares operational overlap and stabilized distinguishability.
-- source:
--   The Information-Disturbance Tradeoff and the Continuity of Stinespring's Representation, arXiv:quant-ph/0605009v1, PDF p. 7, Lemma 2 (Equivalence), Eq. (20)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P49

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Kronecker Topology ENNReal

open Filter

open QAlgorithms.Papers.Independent.Information100.P75 (Mat)

open QAlgorithms.Papers.Independent.Information100.P30 (MatrixMap)

open QAlgorithms.Papers.Independent.Information100.P50 (coefficientMap)

open QAlgorithms.Papers.Independent.Information100.P08 (maximallyMixed)

namespace QAlgorithms.Papers.Independent.Dependency50.P49

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

-- The accepted all-Schatten norms at p=top are exactly the source's operator norms.

local notation "inducedNorm" => QAlgorithms.Papers.Independent.Information100.P50.inducedNorm (⊤ : ℝ≥0∞)

local notation "cbNorm" => QAlgorithms.Papers.Independent.Information100.P50.cbNorm (⊤ : ℝ≥0∞)

/-- PDF p.7, Lemma 2, (20), with root fidelity from p.4. Corrects only the
normalization typo in (19): zero is not a state. No fixed-environment identity is used. -/
theorem operational_fidelity_equivalence {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (T1 T2 : MatrixMap (Fin b) (Fin a))
    (hT1 : IsQuantumChannel T1) (hT2 : IsQuantumChannel T2) :
    1 - operationalFidelity T1 T2 ≤ cbNorm (T1 - T2) / 2 ∧
      cbNorm (T1 - T2) / 2 ≤ Real.sqrt (1 - operationalFidelity T1 T2 ^ 2) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P49

end
