-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P44_tracePolygonObstruction
-- name    : QAlgorithms.Papers.Independent.Information100.P44.tracePolygonObstruction
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T11:36:42.507662+00:00
-- url     : https://prove2.me/theorems/baa8fbd1-2644-4064-b912-a85f73058f6a
-- title:
--   Theorem 4: trace-polygon obstruction for CPTP maps
-- statement:
--   Let $i\ne j$ be input basis states of a nonzero finite system, and fix their nonnegative stochastic transition columns $P_r$ and $Q_r$. Set $a_r=\sqrt{P_rQ_r}$. If for some $r_0$,
--   $$a_{r_0}>\sum_{r\ne r_0}a_r,$$
--   then no CPTP map with those two columns satisfies $|\Phi(|i\rangle\langle j|)_{rr}|=a_r$ for every $r$. Consequently no finite-bath thermal operation does so, for any fixed Hamiltonian and real inverse temperature. This excludes simultaneous saturation and does not assert individual attainability.
-- source:
--   Limitations on Joint Coherence Transfer in Quantum Thermodynamics, arXiv:2608.11872v1, PDF p. 12, Theorem 4: trace-polygon obstruction for CPTP maps

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P44

namespace QAlgorithms.Papers.Independent.Information100.P44

noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

/-- PDF p.12, Theorem 4: fixed transition columns and a strict polygon violation. -/
theorem tracePolygonObstruction {d : ℕ} (hd : 0 < d) (P Q : Fin d → ℝ)
    (hP : ∀ r, 0 ≤ P r) (hQ : ∀ r, 0 ≤ Q r)
    (hPsum : ∑ r, P r = 1) (hQsum : ∑ r, Q r = 1) (i j : Fin d) (hij : i ≠ j)
    (r0 : Fin d) (hstrict : (∑ r ∈ Finset.univ.erase r0, Real.sqrt (P r * Q r)) <
      Real.sqrt (P r0 * Q r0)) :
    (¬ ∃ Phi : Map d, IsChannel Phi ∧
      (∀ r, population Phi r i = P r ∧ population Phi r j = Q r) ∧
      ∀ r, ‖Phi (matrixUnit i j) r r‖ = Real.sqrt (P r * Q r)) ∧
    (∀ (E : Fin d → ℝ) (beta : ℝ), ¬ ∃ Phi : Map d, IsFiniteThermal E beta Phi ∧
      (∀ r, population Phi r i = P r ∧ population Phi r j = Q r) ∧
      ∀ r, ‖Phi (matrixUnit i j) r r‖ = Real.sqrt (P r * Q r)) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P44
