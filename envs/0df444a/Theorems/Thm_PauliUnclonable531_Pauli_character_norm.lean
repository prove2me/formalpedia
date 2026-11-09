-- Prove2me | Theorems.Thm_PauliUnclonable531_Pauli_character_norm
-- name    : PauliUnclonable531.Pauli.character_norm
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:06:17.51613+00:00
-- url     : https://prove2.me/theorems/1d4f41d5-eb20-484a-8ea2-784a79804df6
-- title:
--   Lemma 2.7 — spectral norm of the full character matrix
-- statement:
--   For every n≥0, form the full matrix Ξ with rows and columns indexed by all pairs of n-bit strings and entries Ξₖ,ₗ=(−1)^[k,l]. Its Euclidean operator norm is exactly
--
--   $$\|\Xi\|_\infty=2^n.$$
--
--   This is the full 4ⁿ-square matrix, including its identity row and column. The norm statement is unchanged at n=0, when Ξ is the one-entry matrix [1].
--
--   Differences from the source:
--   - encoding: finite-dimensional complex Hilbert-space operators and binary strings → complex matrices indexed by finite computational bases, Fin 2 bits, real Born probabilities, Euclidean spectral norm and PSD-difference order; reason: these are the same finite-dimensional objects and conventions after choosing the source basis
-- source:
--   Prabhanjan Ananth, Seyoon Ragavan, Amit Sahai, STOC 2027 submission #531 (October 2026), Lemma 2.7, p.13

import Mathlib
import Definitions.Def_PauliUnclonable531_Pauli_Symplectic

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder
set_option autoImplicit false

namespace PauliUnclonable531.Pauli

/-- Lemma 2.7, p.13, on the full 4^n-square matrix, also at n=0. -/
theorem character_norm (n : ℕ) : spectralNorm (character n) = (2 : ℝ)^n := by sorry

end PauliUnclonable531.Pauli
