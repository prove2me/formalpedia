-- Prove2me | Theorems.Thm_PauliUnclonable531_Pauli_choi_identity
-- name    : PauliUnclonable531.Pauli.choi_identity
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-08T11:05:16.247825+00:00
-- url     : https://prove2.me/theorems/b642414b-34cb-4e64-ad11-2a8de9fa9e13
-- title:
--   Theorem 2.1 — normalized Choi trace identity
-- statement:
--   Let A be a nonzero finite input register and B,C arbitrary nonzero finite output registers. Let Φ:L(A)→L(B⊗C) be CPTP, and let M∈L(A), N∈L(B⊗C) be arbitrary operators. With τ=(id⊗Φ)(|Ω⟩⟨Ω|) for the normalized maximally entangled state, one has the complex trace identity
--
--   $$|A|^{-1}\operatorname{Tr}[N\Phi(M)]=\operatorname{Tr}[(M^T\otimes N)\tau].$$
--
--   The transpose is ordinary transpose in the chosen matching reference basis. No Hermiticity or positivity is imposed on the test operators, and the output dimension is unrelated to the input dimension. This fixes the normalization used by the game reduction.
--
--   Differences from the source:
--   - encoding: finite-dimensional complex Hilbert-space operators and binary strings → complex matrices indexed by finite computational bases, Fin 2 bits, real Born probabilities, Euclidean spectral norm and PSD-difference order; reason: these are the same finite-dimensional objects and conventions after choosing the source basis
-- source:
--   Prabhanjan Ananth, Seyoon Ragavan, Amit Sahai, STOC 2027 submission #531 (October 2026), Theorem 2.1, pp.10–11

import Mathlib
import Definitions.Def_PauliUnclonable531_Pauli_Choi

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder
set_option autoImplicit false

namespace PauliUnclonable531.Pauli

/-- Theorem 2.1, pp.10–11. Ordinary transpose, normalized Choi, arbitrary test operators. -/
theorem choi_identity {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] [Nonempty A] [Nonempty B] [Nonempty C]
    (Φ : Op A →ₗ[ℂ] Op (B × C)) (hΦ : WildeQIT.EntBreaking.IsQuantumChannel Φ)
    (M : Op A) (N : Op (B × C)) :
    (Fintype.card A : ℂ)⁻¹ * (N * Φ M).trace =
      (Matrix.kronecker M.transpose N * choi Φ).trace := by sorry

end PauliUnclonable531.Pauli
