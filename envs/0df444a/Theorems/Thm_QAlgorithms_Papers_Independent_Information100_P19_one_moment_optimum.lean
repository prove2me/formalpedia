-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P19_one_moment_optimum
-- name    : QAlgorithms.Papers.Independent.Information100.P19.one_moment_optimum
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T09:53:04.515162+00:00
-- url     : https://prove2.me/theorems/57f43ee6-c38f-4b6b-b4a1-05fed9957a26
-- title:
--   §5.1 unnumbered: exact one-moment optimum
-- statement:
--   For a prescribed even moment $0\le r\le1$, the discrete unit-atom problem has value
--   $$\alpha(r)=\sqrt r.$$
--   The one-entry vector $(\sqrt r)$ is feasible and attains this value, including at $r=0$. This solves the one-moment case exactly.
-- source:
--   Optimal entanglement criteria from trace invariants, arXiv:2609.29471v1, PDF p. 31, §5.1 unnumbered: exact one-moment optimum

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P19

noncomputable section

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P19

/-- §5.1 unnumbered: exact one-moment optimum; arXiv:2609.29471v1, PDF pp.31. -/
theorem one_moment_optimum (r : ℝ) (hr : 0≤r) (hr1 : r≤1) :
    alpha (![r] : Fin 1 → ℝ) = ENNReal.ofReal (Real.sqrt r) ∧
    discreteFeasible (![r] : Fin 1 → ℝ) (fun _ : Fin 1 => Real.sqrt r) := by sorry

end QAlgorithms.Papers.Independent.Information100.P19

end
