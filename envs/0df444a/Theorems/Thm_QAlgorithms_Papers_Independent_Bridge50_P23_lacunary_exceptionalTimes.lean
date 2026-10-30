-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P23_lacunary_exceptionalTimes
-- name    : QAlgorithms.Papers.Independent.Bridge50.P23.lacunary_exceptionalTimes
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:23:26.704758+00:00
-- url     : https://prove2.me/theorems/64ced7a3-52c5-4457-ba83-92b075a5b097
-- title:
--   §II remark: infinitely many exceptional time scales
-- statement:
--   All systems are nonzero separable complex Hilbert spaces. States are positive trace-class operators of trace one. Trace norms have no factor one half, except where displayed. For an integer $c\ge3$ let $H_c|n\rangle=c^n|n\rangle$, and put $\tau_k=2\pi c^{-k}$ for $k\ge0$. In the unitary $U_{c,k}=e^{-i\tau_k H_c}$, every diagonal phase with $n\ge k$ is one. Furthermore, for each fixed $k$ and every $a>0$, $$\exists c_0\ge3\ \forall c\in\mathbb N,\ c\ge c_0:\quad\|U_{c,k}-I\|_{\mathrm{op}}<a.$$ The diagonal operator norm is the supremum of its diagonal moduli. These examples give infinitely many exceptional time scales.
-- source:
--   Energy-constrained diamond norm with applications to the uniform continuity of continuous variable channel capacities, arXiv:1712.10267v1, PDF p. 4, §II remark: infinitely many exceptional time scales

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P23

noncomputable section

open Filter

open scoped ENNReal NNReal BigOperators Topology

namespace QAlgorithms.Papers.Independent.Bridge50.P23

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State PureState IsTraceClass traceSize tensorApply rankOne productCoeff)

open QAlgorithms.Papers.Independent.Frontier18.P01
  (Channel traceSecond traceFirst homogeneousEntropy generalizedRelativeEntropy
   channelTensorAction finiteInputCoherentInfo)

open QAlgorithms.Papers.Independent.Frontier18.P08 (IsQuantumOperation)

open QAlgorithms.Papers.Independent.Claimed50.P13
  (PositiveObservable closedFormExpectation GibbsCondition TensorBlockIndex blockAction blockEnergy)

open QAlgorithms.Papers.Independent.Claimed50.P18 (finiteFirstConditionalEntropy)

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Section II remark, PDF p.4: lacunary exceptional times. Printed positive
unitary phase is replaced by the negative phase of Proposition 2. Conjugating
all phases preserves the claimed operator norm closeness. No conjectural
essential-period characterization is asserted. -/
theorem lacunary_exceptionalTimes (k : ℕ) :
    (∀ c : ℕ, 3 ≤ c → ∀ n : ℕ, k ≤ n →
      Complex.exp (-Complex.I * ((2 * Real.pi / (c : ℝ) ^ k) * (c : ℝ) ^ n : ℝ)) = 1) ∧
    (∀ e : ℝ, 0 < e → ∃ c0 : ℕ, 3 ≤ c0 ∧ ∀ c : ℕ, c0 ≤ c →
      diagonalUnitaryDistance (fun n => (c : ℝ) ^ n) (2 * Real.pi / (c : ℝ) ^ k) <
        ENNReal.ofReal e) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P23

end
