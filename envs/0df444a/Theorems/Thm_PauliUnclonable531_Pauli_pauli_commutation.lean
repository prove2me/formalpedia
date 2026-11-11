-- Prove2me | Theorems.Thm_PauliUnclonable531_Pauli_pauli_commutation
-- name    : PauliUnclonable531.Pauli.pauli_commutation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-08T11:06:28.845251+00:00
-- url     : https://prove2.me/theorems/20e7e01e-8687-4dee-bf18-cb29286a6b7a
-- title:
--   Lemma 2.5 — Pauli commutation and transposed commutation
-- statement:
--   For every n≥0 and any two full Pauli labels k,l, let [k,l] be their symplectic form in the field with two elements. Both relations hold:
--
--   $$P_kP_l=(-1)^{[k,l]}P_lP_k,\qquad P_k^TP_l^T=(-1)^{[k,l]}P_l^TP_k^T.$$
--
--   Identity labels are included. These signs supply the algebraic relation used in the selected Proof A of the correlation product estimate.
--
--   Differences from the source:
--   - encoding: finite-dimensional complex Hilbert-space operators and binary strings → complex matrices indexed by finite computational bases, Fin 2 bits, real Born probabilities, Euclidean spectral norm and PSD-difference order; reason: these are the same finite-dimensional objects and conventions after choosing the source basis
-- source:
--   Prabhanjan Ananth, Seyoon Ragavan, Amit Sahai, STOC 2027 submission #531 (October 2026), Lemma 2.5, p.12, Eq. (14)

import Mathlib
import Definitions.Def_PauliUnclonable531_Pauli_Symplectic

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder
set_option autoImplicit false

namespace PauliUnclonable531.Pauli

/-- Lemma 2.5, p.12, including both the original and the transposed relation. -/
theorem pauli_commutation (n : ℕ) (k l : Label n) :
    pauli k * pauli l = sign (symplectic k l) • (pauli l * pauli k) ∧
    (pauli k).transpose * (pauli l).transpose =
      sign (symplectic k l) • ((pauli l).transpose * (pauli k).transpose) := by sorry

end PauliUnclonable531.Pauli
