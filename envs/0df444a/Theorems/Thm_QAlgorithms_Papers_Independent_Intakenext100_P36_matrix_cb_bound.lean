-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P36_matrix_cb_bound
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P36.matrix_cb_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:13:30.481744+00:00
-- url     : https://prove2.me/theorems/0befb3ae-0a9f-4a94-b675-d152836707d6
-- title:
--   Corollary 7: the minimum of the input and output dimension bounds
-- statement:
--   Let $n,k\ge1$, and let $\phi:M_n\to M_k$ be any complex-linear map on all matrices. With Euclidean operator norms on matrices and their induced map norms,
--
--   $$\|\phi\|_{\rm cb}\le\min\{k,\sqrt{n^3}\}\,\|\phi\|.$$
--
--   The ordinary induced norm is finite. The CB norm is the supremum over all positive finite ancilla dimensions; no positivity, unitality, or trace-preservation hypothesis is imposed on $\phi$.
--
--   This combines the output-dimension stabilization estimate with the arbitrary-operator-space estimate of Theorem 6.
-- source:
--   Computing Stabilized Norms for Quantum Operations via the Theory of Completely Bounded Maps, arXiv:0711.3636v1, PDF p. 5, Corollary 7

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P36

noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

namespace QAlgorithms.Papers.Independent.Intakenext100.P36

local notation "Mat" => QAlgorithms.Papers.Independent.Information100.P50.M

local notation "Map" => QAlgorithms.Papers.Independent.Information100.P50.Lin

open QAlgorithms.Papers.Independent.Dependency50.P49 (traceDual)

/-- Corollary 7, PDF p.5: the radical covers n cubed. -/
theorem matrix_cb_bound {n k : ℕ} (hn : 0 < n) (hk : 0 < k) (phi : Map n k) :
    extendedInducedNorm phi < ⊤ ∧
    extendedCBNorm phi ≤ ENNReal.ofReal (min (k : ℝ) (Real.sqrt ((n : ℝ) ^ 3))) *
      extendedInducedNorm phi := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P36

end
