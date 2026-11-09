-- Prove2me | Theorems.Thm_PauliUnclonable531_Pauli_pauli_bridges
-- name    : PauliUnclonable531.Pauli.pauli_bridges
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:05:34.064205+00:00
-- url     : https://prove2.me/theorems/b038b674-0fb3-4e14-a2c3-559493736d0d
-- title:
--   Proposition 2.3 — residual involution and transpose identities; core: LockingAccInfo.lemma6_pauliString
-- statement:
--   For every n≥0 and full label k=(x,z), let Pₖ be its tensor Pauli. The residual identities are
--
--   $$P_k^2=I,\qquad (P_k^T)^2=I,\qquad P_k^T=(-1)^{\sum_jx_jz_j}P_k.$$
--
--   Together with the existing Open item LockingAccInfo.lemma6_pauliString (Hermiticity, trace, spectrum and orthogonality), these identities retain the full Proposition 2.3 obligation, including transposes. The existing item is unresolved support, not an assumed proved fact. This item states only the residual identities, including the sign identified in the source proof; it does not duplicate the referenced core.
--
--   Differences from the source:
--   - encoding: finite-dimensional complex Hilbert-space operators and binary strings → complex matrices indexed by finite computational bases, Fin 2 bits, real Born probabilities, Euclidean spectral norm and PSD-difference order; reason: these are the same finite-dimensional objects and conventions after choosing the source basis
--   - encoding: the full Proposition 2.3, including Hermiticity, tracelessness and orthogonality → the referenced Open core plus this explicitly titled residual involution/transpose item; reason: the core is already posed; transposing its equalities and using the displayed sign recovers every source clause
-- source:
--   Prabhanjan Ananth, Seyoon Ragavan, Amit Sahai, STOC 2027 submission #531 (October 2026), Proposition 2.3 and its proof, p.12

import Mathlib
import Definitions.Def_PauliUnclonable531_Pauli_Keys

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder
set_option autoImplicit false

namespace PauliUnclonable531.Pauli

/-- Proposition 2.3 residual clauses, p.12, alongside the referenced Open
LockingAccInfo.lemma6_pauliString core. No orthogonality/Hermiticity duplicate is posed. -/
theorem pauli_bridges (n : ℕ) (k : Label n) :
    pauli k * pauli k = 1 ∧
    (pauli k).transpose * (pauli k).transpose = 1 ∧
    (pauli k).transpose = sign (∑ j, k.1 j * k.2 j) • pauli k := by sorry

end PauliUnclonable531.Pauli
