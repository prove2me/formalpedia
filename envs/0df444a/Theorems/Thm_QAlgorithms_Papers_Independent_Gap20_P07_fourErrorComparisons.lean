-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P07_fourErrorComparisons
-- name    : QAlgorithms.Papers.Independent.Gap20.P07.fourErrorComparisons
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:19:38.430979+00:00
-- url     : https://prove2.me/theorems/15283055-232b-45a7-8a81-5fce1b4d4a94
-- title:
--   Proposition 4.3 / (39): four dimension-independent error comparisons
-- statement:
--   Let $T$ be a CPTP endomorphism of a finite-dimensional nonzero complex system. Let $F_{\min}(T)$ be the minimum normalized pure-state fidelity, $F_{e,\min}(T)$ the infimum of squared entanglement fidelity over density operators, $a=\|T-\mathrm{id}\|_{1\to1}$, and $b=\|T-\mathrm{id}\|_{\rm cb}$, with the full trace norm convention. Then
--   $$1-F_{e,\min}(T)\le4\sqrt{1-F_{\min}(T)}\le4\sqrt a\le4\sqrt b\le8(1-F_{e,\min}(T))^{1/4}.$$
--   Every constant and the fourth root are dimension independent. This chain explains equivalence of these four error criteria near an ideal channel.
-- source:
--   Tema Con Variazioni: Quantum Channel Capacity, arXiv:quant-ph/0311037v1, PDF p. 13, Proposition 4.3 / (39): four dimension-independent error comparisons

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

/-- PDF pp.13--14, Proposition 4.3, (39): the complete four-inequality chain,
with constants 4,4,4,8 and the final fourth root. -/
theorem fourErrorComparisons (d : ℕ) (hd : 0 < d)
    (T : Superop (Fin d) (Fin d)) (hT : IsChannel T) :
    1 - minimumFe d T ≤ 4 * Real.sqrt (1 - minimumFidelity d T) ∧
    4 * Real.sqrt (1 - minimumFidelity d T) ≤ 4 * Real.sqrt (ordinaryNorm d (fun X => T X - X)) ∧
    4 * Real.sqrt (ordinaryNorm d (fun X => T X - X)) ≤ 4 * Real.sqrt (finiteCbNorm d (fun X => T X - X)) ∧
    4 * Real.sqrt (finiteCbNorm d (fun X => T X - X)) ≤
      8 * Real.rpow (1 - minimumFe d T) (1 / 4 : ℝ) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P07

end
