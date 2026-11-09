-- Prove2me | Theorems.Thm_PauliUnclonable531_Pauli_preparation
-- name    : PauliUnclonable531.Pauli.preparation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:09:57.817752+00:00
-- url     : https://prove2.me/theorems/36b747f5-051c-4b07-856c-84acf766297c
-- title:
--   Proposition 3.2 — the explicit product-state ensemble
-- statement:
--   For every n≥1, supported key k=(x,z) and message bit m, let qⱼ mark the nonidentity factors and let Uₖ be the tensor product of I,H,SH prescribed on p.16. Then
--
--   $$\rho_{k,m}=2^{-(n-1)}\sum_{r:\,\bigoplus_jq_jr_j=m}U_k|r\rangle\langle r|U_k^\dagger.$$
--
--   By definition ρₖ,ₘ=2⁻ⁿ(I+(−1)ᵐPₖ), so this is the full chain of equalities in (15). It identifies the averaged product-state ensemble with the ciphertext, and retains the unconstrained random bits at identity positions.
--
--   Differences from the source:
--   - encoding: finite-dimensional complex Hilbert-space operators and binary strings → complex matrices indexed by finite computational bases, Fin 2 bits, real Born probabilities, Euclidean spectral norm and PSD-difference order; reason: these are the same finite-dimensional objects and conventions after choosing the source basis
-- source:
--   Prabhanjan Ananth, Seyoon Ragavan, Amit Sahai, STOC 2027 submission #531 (October 2026), Proposition 3.2, p.16, Eq. (15)

import Mathlib
import Definitions.Def_PauliUnclonable531_Pauli_Ensemble

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder
set_option autoImplicit false

namespace PauliUnclonable531.Pauli

/-- Proposition 3.2, Eq. (15), p.16; n≥1 is the construction's standing assumption. -/
theorem preparation (n : ℕ) (hn : 1 ≤ n) (k : Key n) (m : Fin 2) :
    ciphertext k m = parityEnsemble k m := by sorry

end PauliUnclonable531.Pauli
