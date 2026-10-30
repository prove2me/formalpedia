-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P17_stabilizedAverage
-- name    : QAlgorithms.Papers.Independent.Advance50.P17.stabilizedAverage
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T11:31:25.170041+00:00
-- url     : https://prove2.me/theorems/5cb2fda1-2c53-4fe3-a306-5fa82aceb191
-- title:
--   Section IV B: large-ancilla averaged distances converge to process distance
-- statement:
--   Fix CPTP maps $\mathcal E,\mathcal F$ on a positive finite-dimensional system, and choose $\Delta\in\{D,A,B,C\}$. With normalized Haar averages on the enlarged registers,
--
--   $$\lim_{m\to\infty}\Delta_{\rm ave}(\mathcal I_m\otimes\mathcal E,\mathcal I_m\otimes\mathcal F)=\Delta_{\rm pro}(\mathcal E,\mathcal F).$$
--
--   Here $m$ ranges over positive integer ancilla dimensions. The assertion includes existence of this limit and identifies it with the normalized Choi-state distance.
-- source:
--   Distance measures to compare real and ideal quantum processes, arXiv:quant-ph/0408063v2, PDF p. 7, Section IV B: large-ancilla averaged distances converge to process distance

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P17

noncomputable section

open MeasureTheory Filter

open scoped Matrix ComplexConjugate Topology

namespace QAlgorithms.Papers.Independent.Advance50.P17

open QAlgorithms.Papers.Independent.Information100.P53 (fidelity)

open QAlgorithms.Papers.Independent.Information100.P08 (canonicalPurification)

open QAlgorithms.Papers.Independent.Information100.P75 (hermitianReal)

variable {I J K : Type} [Fintype I] [Fintype J] [Fintype K]
  [DecidableEq I] [DecidableEq J] [DecidableEq K]
  [Nonempty I] [Nonempty J] [Nonempty K]

/-- Section IV B, PDF p.7: the actual large-ancilla Haar averages converge to process distance,
for the four concrete candidates. Using m+1 indexes all positive ancilla sizes. -/
theorem stabilizedAverage (c : Choice) (E F : FiniteProcess I I) :
    Tendsto (fun m : ℕ => aveDistance (stateDistance c)
      (idTensorSuperop (R := Fin (m + 1)) E.val)
      (idTensorSuperop (R := Fin (m + 1)) F.val)) atTop
      (𝓝 (proDistance (stateDistance c) E.val F.val)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P17

end
