-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P29_entanglementFidelity_inputContinuity
-- name    : QAlgorithms.Papers.Independent.Gap48.P29.entanglementFidelity_inputContinuity
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T04:12:24.626796+00:00
-- url     : https://prove2.me/theorems/6ced482a-df70-4411-bc7d-37c053189647
-- title:
--   Continuity of entanglement fidelity in its input
-- statement:
--   Let $B$ and $B+\Delta$ be density operators on the same nonzero finite-dimensional Hilbert space, and let $\mathcal A$ be a completely positive trace-nonincreasing operation. Write $\|\Delta\|_1=\operatorname{tr}\sqrt{\Delta^\dagger\Delta}$ for the unhalved trace norm. Then
--
--   $$|F_e(B+\Delta,\mathcal A)-F_e(B,\mathcal A)|\leq\|\Delta\|_1^2+2\|\Delta\|_1.$$
--
--   This controls the change of unrenormalized entanglement fidelity when the input state changes.
-- source:
--   On Quantum Fidelities and Channel Capacities, arXiv:quant-ph/9809010v1, PDF p. 5, Lemma 5, Eq.(36)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P29

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P29

open QAlgorithms Filter

open scoped Matrix ComplexConjugate ComplexOrder Topology

open QAlgorithms.Papers.Independent.Information100.P07 (IsProjection)

open QAlgorithms.Papers.Independent.Information100.P67 (squaredFidelity)

/-- PDF p.5, Lemma 5, Eq.(36): continuity between density inputs. B is a baseline
state and Delta their difference; unrenormalized refers to the CP TNI operation. -/
theorem entanglementFidelity_inputContinuity {I : Type*} [Fintype I] [DecidableEq I]
    [Nonempty I] (B Delta : Matrix I I ℂ) (hB : IsDensityMatrix B)
    (hBD : IsDensityMatrix (B + Delta)) (A : Superop I I) (hA : TraceNonincreasingCPMap A) :
    |fe (B + Delta) A - fe B A| ≤ traceNorm Delta ^ 2 + 2 * traceNorm Delta := by sorry

end QAlgorithms.Papers.Independent.Gap48.P29

end
