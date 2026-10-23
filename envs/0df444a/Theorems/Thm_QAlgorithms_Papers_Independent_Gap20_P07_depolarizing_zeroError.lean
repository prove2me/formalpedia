-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P07_depolarizing_zeroError
-- name    : QAlgorithms.Papers.Independent.Gap20.P07.depolarizing_zeroError
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:08:03.144994+00:00
-- url     : https://prove2.me/theorems/46aaea63-0881-4b06-ba86-fa29bd19bf1e
-- title:
--   Section 2.7: depolarizing noise prevents exact qubit transmission
-- statement:
--   For an integer $d\ge2$ and $0<p\le1$, let $T_p(X)=(1-p)X+p\operatorname{tr}(X)I_d/d$. For every positive block length $n$, the optimal full-cb error of simulating one ideal qubit through $T_p^{\otimes n}$ satisfies
--   $$\Delta(T_p^{\otimes n},\mathrm{id}_2)>0.$$
--   Consequently its capacity defined by eventual exactly vanishing error is zero. This statement concerns perfect transmission and does not set the ordinary approximate quantum capacity to zero.
-- source:
--   Tema Con Variazioni: Quantum Channel Capacity, arXiv:quant-ph/0311037v1, PDF p. 6, Section 2.7: depolarizing noise prevents exact qubit transmission

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

/-- PDF p.6: any positive replacement probability prevents exact qubit transmission
through every finite positive block, without asserting that approximate Q is zero. -/
theorem depolarizing_zeroError (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) :
    let T := QuditFidelity.depolarizingMap d (by omega) p
    (∀ n : ℕ+, 0 < codingSimulationDistance (traceClassChannelPower T n)
      (id : Operation (Fin 2) (Fin 2))) ∧ finiteErrorCapacity T 0 = 0 := by sorry

end QAlgorithms.Papers.Independent.Gap20.P07

end
