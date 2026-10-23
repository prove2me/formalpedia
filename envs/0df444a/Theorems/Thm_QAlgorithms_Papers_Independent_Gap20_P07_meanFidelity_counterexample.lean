-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P07_meanFidelity_counterexample
-- name    : QAlgorithms.Papers.Independent.Gap20.P07.meanFidelity_counterexample
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:21:40.22406+00:00
-- url     : https://prove2.me/theorems/ca2e29f0-a2c4-45d1-a021-ef0e35366c7e
-- title:
--   Section 4.3 / (51)–(53): high mean fidelity without norm convergence
-- statement:
--   For each integer $d\ge2$, let $P_+=|e_1\rangle\langle e_1|$, $P_-=I-P_+$, and define the CPTP pinching channel $T_d(X)=P_+XP_++P_-XP_-$. Then
--   $$F_c(T_d)=\frac{d^2-2d+2}{d^2},\qquad\lim_{d\to\infty}F_c(T_d)=\lim_{d\to\infty}F_{\rm av}(T_d)=1,\qquad\|T_d-\mathrm{id}\|_{1\to1}\ge1.$$
--   Thus no function $g$ with $g(x)\to0$ as $x\uparrow1$ can give $\|T-\mathrm{id}\|_{1\to1}\le g(F_c(T))$ uniformly over all positive dimensions and CPTP endomorphisms. This counterexample does not contradict equality of capacities, where logical subspaces may be selected.
-- source:
--   Tema Con Variazioni: Quantum Channel Capacity, arXiv:quant-ph/0311037v1, PDF p. 16, Section 4.3 / (51)–(53): high mean fidelity without norm convergence

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

/-- PDF p.16, (51)--(53): the actual firstCoordinatePinching family has high mean/channel
fidelity and ordinary-norm distance bounded below by one. The two-dimensional
superposition gives off-diagonal eigenvalues +1/2 and -1/2, hence full trace norm one. -/
theorem meanFidelity_counterexample :
    (∀ d : ℕ+, 2 ≤ (d : ℕ) → IsChannel (firstCoordinatePinching d) ∧
      QuditFidelity.entanglementFidelity d d.pos (firstCoordinatePinching d) =
        ((d : ℝ)^2 - 2 * d + 2) / (d : ℝ)^2 ∧
      1 ≤ ordinaryNorm d (fun X => firstCoordinatePinching d X - X)) ∧
    Tendsto (fun n : ℕ => QuditFidelity.averageFidelity (n + 2) (by omega)
      (firstCoordinatePinching ⟨n + 2, by omega⟩)) atTop (𝓝 1) ∧
    Tendsto (fun n : ℕ => QuditFidelity.entanglementFidelity (n + 2) (by omega)
      (firstCoordinatePinching ⟨n + 2, by omega⟩)) atTop (𝓝 1) ∧
    ¬ ∃ f : ℝ → ℝ, Tendsto f (𝓝[<] (1 : ℝ)) (𝓝 0) ∧
      ∀ (d : ℕ) (hd : 0 < d) (T : Superop (Fin d) (Fin d)), IsChannel T →
        ordinaryNorm d (fun X => T X - X) ≤ f (QuditFidelity.entanglementFidelity d hd T) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P07

end
