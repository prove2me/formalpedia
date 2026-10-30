-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P17_finite_packaged_comparison
-- name    : QAlgorithms.Papers.Independent.Extend50.P17.finite_packaged_comparison
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:53:14.817385+00:00
-- url     : https://prove2.me/theorems/d359a553-4fbc-446f-bf11-ff836046a4c5
-- title:
--   Unnumbered comparison of the two fidelity bounds
-- statement:
--   For integers $4\le k$ and $2k\le N$, define the qubit MPBT binomial lower bound $B(N,k)=\binom Nk/\binom{N+3}k$ and the packaged estimate $P(N,k)=(1-3k/(4N))^k$. Then
--
--   $$P(N,k)<B(N,k).$$
--
--   This compares two numerical lower bounds. It does not identify $P$ with the actual packaged fidelity or assert dominance over the actual packaged protocol.
-- source:
--   Multiport based teleportation -- transmission of a large amount of quantum information, arXiv:2008.00856v3, PDF p. 4, Unnumbered comparison of the two fidelity bounds

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P17

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P17

open Filter MeasureTheory

open scoped BigOperators Matrix ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

/-- PDF p.4, comparison following Eq.(12): compare the two BOUNDS, for qubits. -/
theorem finite_packaged_comparison (N k : ℕ) (hk : 4 ≤ k) (hNk : 2*k ≤ N) :
    packagedLower N k < binomialBound 2 N k := by sorry

end QAlgorithms.Papers.Independent.Extend50.P17

end
