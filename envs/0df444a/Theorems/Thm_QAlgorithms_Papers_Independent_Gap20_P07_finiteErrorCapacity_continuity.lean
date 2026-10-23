-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P07_finiteErrorCapacity_continuity
-- name    : QAlgorithms.Papers.Independent.Gap20.P07.finiteErrorCapacity_continuity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:08:58.669905+00:00
-- url     : https://prove2.me/theorems/82c7ae7c-ef45-4a0e-816c-8aa01e637b48
-- title:
--   Sections 2.7 and 7.3 / (108): finite-error capacities approach Q
-- statement:
--   Let $T$ be any memoryless CPTP channel between nonzero complex Hilbert spaces. Define $Q_\epsilon(T)$ exactly as Definition 2.1, but require eventual optimal full-cb error at most $\epsilon$. For $0<\epsilon<1/(4e)$, where $e=\exp(1)$,
--   $$Q_\epsilon(T)\ge Q(T)\ge(1-4e\epsilon)Q_\epsilon(T),\qquad\lim_{\epsilon\downarrow0}Q_\epsilon(T)=Q(T).$$
--   Capacities and scalar multiplication are extended nonnegative. The strict positivity of $\epsilon$ avoids the distinct zero-error condition.
-- source:
--   Tema Con Variazioni: Quantum Channel Capacity, arXiv:quant-ph/0311037v1, PDF p. 6, Sections 2.7 and 7.3 / (108): finite-error capacities approach Q

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

/-- PDF pp.6,29, (108): full-cb finite-error capacities converge from the right;
positive epsilon and positive scalar factor exclude the zero-error endpoint. -/
theorem finiteErrorCapacity_continuity {I J : Type} [Nonempty I] [Nonempty J]
    (T : Operation I J) (hT : IsTraceClassChannel T) :
    (∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 / (4 * Real.exp 1) →
      qubitReferenceCapacity T ≤ finiteErrorCapacity T epsilon ∧
      finiteErrorCapacity T epsilon * ENNReal.ofReal (1 - 4 * Real.exp 1 * epsilon) ≤
        qubitReferenceCapacity T) ∧
    Tendsto (finiteErrorCapacity T) (𝓝[>] (0 : ℝ)) (𝓝 (qubitReferenceCapacity T)) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P07

end
