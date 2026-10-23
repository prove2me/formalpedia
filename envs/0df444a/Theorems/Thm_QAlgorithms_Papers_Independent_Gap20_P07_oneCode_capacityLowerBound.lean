-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P07_oneCode_capacityLowerBound
-- name    : QAlgorithms.Papers.Independent.Gap20.P07.oneCode_capacityLowerBound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:28:53.065712+00:00
-- url     : https://prove2.me/theorems/eac7eb8a-49fb-4d4e-b31a-6939244092d9
-- title:
--   Proposition 7.2 / (107): one successful code yields a capacity lower bound
-- statement:
--   Let $T$ be a memoryless CPTP channel between arbitrary nonzero complex Hilbert spaces. Suppose a CPTP code sends a $d$-level system, where $d$ is prime, through $N\ge1$ channel uses, with actual full-cb error $\Delta<1/(2e)$ and $e=\exp(1)$. Writing $H_2$ for binary entropy in bits, put
--   $$B(N,d,\Delta)=\frac{\log_2d}{N}(1-4e\Delta)-\frac{H_2(2e\Delta)}{N}.$$
--   Then $Q(T)\ge\max\{B(N,d,\Delta),0\}$, and every positive $R<B(N,d,\Delta)$ admits all-block codes with some positive exponential error exponent. Furthermore
--   $$Q(T)=\sup_{\text{all such actual prime-dimensional codes}}\max\{B(N,d,\Delta),0\}.$$
--   The supremum is extended nonnegative and is zero if the set is empty. Logical and physical dimensions may differ, and $\Delta=0$ is valid. This retains the lower bound, least-upper-bound clause, and exponential reliability conclusion.
-- source:
--   Tema Con Variazioni: Quantum Channel Capacity, arXiv:quant-ph/0311037v1, PDF p. 28, Proposition 7.2 / (107): one successful code yields a capacity lower bound

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P07

noncomputable section

open Filter MeasureTheory

open scoped Topology ENNReal NNReal Matrix ComplexOrder ComplexConjugate

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace QAlgorithms.Papers.Independent.Gap20.P07

open QAlgorithms

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsTraceClass IsTraceClassChannel traceSize rankOne tensorApply)

open QAlgorithms.Papers.Independent.Frontier30.P14
  (Operation isometryCoeff conjugateKernel)

open QAlgorithms.Papers.Independent.Claimed50.P35
  (stabilizedTraceClassNorm traceClassTensorMap traceClassChannelPower
   transpose transposeBound TraceLinear tracePair MeasurePrepare)

open QAlgorithms.Papers.Independent.Gap48.P29 (fe FiniteCPMap)

/-- PDF pp.28--29, Proposition 7.2, (107): actual prime-dimensional code,
positive N, the entire lower bound, least-upper-bound clause, and exponential
reliability at every positive strict subrate. Empty prime-code supremum is zero. -/
theorem oneCode_capacityLowerBound {I J : Type} [Nonempty I] [Nonempty J]
    (T : Operation I J) (hT : IsTraceClassChannel T) :
    (∀ (N : ℕ+) (d : ℕ), Nat.Prime d → ∀ C : TraceClassBlockCode T N d,
      C.error < ENNReal.ofReal (1 / (2 * Real.exp 1)) →
      ENNReal.ofReal (hashingBound N d C.error.toReal) ≤ qubitReferenceCapacity T ∧
      ∀ R : ℝ, 0 < R → R < hashingBound N d C.error.toReal → ExponentialReliable T R) ∧
    qubitReferenceCapacity T = hashingSupremum T := by sorry

end QAlgorithms.Papers.Independent.Gap20.P07

end
