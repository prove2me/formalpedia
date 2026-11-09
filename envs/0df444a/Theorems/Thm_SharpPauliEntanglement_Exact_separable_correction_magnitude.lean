-- Prove2me | Theorems.Thm_SharpPauliEntanglement_Exact_separable_correction_magnitude
-- name    : SharpPauliEntanglement.Exact.separable_correction_magnitude
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:52:27.840761+00:00
-- url     : https://prove2.me/theorems/3c4c102f-14db-4e48-8fd8-1d6147bb012c
-- title:
--   Lemma 3.1 — Hermitian correction rI+A is in the product-Pauli separable cone for r≥∥A∥P,1
-- statement:
--   Let $A$ be a Hermitian operator on $n$ qubits and let $r\in\mathbb R$ satisfy $r\ge\|A\|_{P,1}$, where the norm is the sum of absolute values of all tensor-Pauli coefficients. Then
--
--   $$rI+A\in\operatorname{cone}\left\{\bigotimes_{q=1}^n\frac{I+s_qP_q}{2}:P_q\in\{X,Y,Z\},\ s_q\in\{-1,1\}\right\}.$$
--
--   Thus the shifted operator is a nonnegative finite sum of product Pauli eigenprojectors. The conclusion is unnormalized and includes zero; it supplies the separable factors of the Gibbs decomposition.
--
--   Differences from the source:
--   - encoding: arbitrary finite qubit and term labels → computational bitstrings and Fin n, Fin m labels; reason: finite reindexing preserves every matrix, support relation and source instance
-- source:
--   Bobak T. Kiani, Sharp universal death of entanglement threshold for Pauli Hamiltonians, STOC 2027 submission #159 (October 2026), printed/PDF p. 9, Lemma 3.1

import Definitions.Def_SharpPauliEntanglement_Exact_PauliModel

set_option autoImplicit false
noncomputable section

attribute [local instance] Classical.decEq Classical.propDecidable
open scoped BigOperators
namespace SharpPauliEntanglement.Exact

/-- Kiani, submission #159, p. 9, Lemma 3.1. The conclusion is a cone, not a hull. -/
theorem separable_correction_magnitude {n : ℕ} (A : Op (Fin n)) (r : ℝ)
    (hA : A.IsHermitian) (hr : pauliNorm A ≤ r) :
    PauliSeparableCone ((r : ℂ) • 1 + A) := by sorry

end SharpPauliEntanglement.Exact
