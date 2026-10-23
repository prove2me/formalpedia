-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P07_unconstrainedEntropyCapacity_infinite
-- name    : QAlgorithms.Papers.Independent.Gap20.P07.unconstrainedEntropyCapacity_infinite
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:06:15.670374+00:00
-- url     : https://prove2.me/theorems/f2fa61ec-a8cb-4d1c-8239-8bd4a48264c3
-- title:
--   Sections 2.6 and 4.4: infinite unconstrained Schumacher capacity
-- statement:
--   Let $T$ be a memoryless CPTP channel between nonzero complex Hilbert spaces with $Q(T)>0$. If arbitrary finite block source dimensions are permitted, then
--   $$Q_{\rm entropy,unconstrained}(T)=+\infty.$$
--   More explicitly, there are positive integer dimensions $d_n,k_n$, numbers $0<\epsilon_n<1$ tending to zero, and source states
--   $$\rho_n=(1-\epsilon_n)\frac{I_{d_n}}{d_n}\oplus\epsilon_n\frac{I_{k_n}}{k_n}$$
--   with CPTP codes defined on the entire enlarged space, whose entanglement fidelity tends to one while $S(\rho_n)/n\to+\infty$. This construction explains why a dimension or QAEP restriction is necessary for the entropy formulation.
-- source:
--   Tema Con Variazioni: Quantum Channel Capacity, arXiv:quant-ph/0311037v1, PDF p. 6, Sections 2.6 and 4.4: infinite unconstrained Schumacher capacity

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

/-- PDF pp.6,19, (67)--(68): unconstrained entropy capacity is infinite if Q>0.
The witness is the actual direct-sum mixture and uses TP codes on its whole space. -/
theorem unconstrainedEntropyCapacity_infinite {I J : Type} [Nonempty I] [Nonempty J]
    (T : Operation I J) (hT : IsTraceClassChannel T) (hQ : 0 < qubitReferenceCapacity T) :
    sourceEntropyCapacity T (fun _ => True) = ⊤ ∧
    ∃ (d k : ℕ → ℕ+) (epsilon : ℕ → ℝ) (S : QuantumSource),
      (∀ n, 0 < epsilon n ∧ epsilon n < 1) ∧ Tendsto epsilon atTop (𝓝 0) ∧
      (∀ n, S.dimension n = d n + k n) ∧
      (∀ n, HEq (S.rho n) (enlargedMixture (d n) (k n) (epsilon n))) ∧
      SourceReliable T S ∧
      Tendsto (fun n => ENNReal.ofReal (vnEntropy (S.rho n) / (n + 1 : ℝ))) atTop (𝓝 ⊤) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P07

end
