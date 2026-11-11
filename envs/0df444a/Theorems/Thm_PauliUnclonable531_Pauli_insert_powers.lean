-- Prove2me | Theorems.Thm_PauliUnclonable531_Pauli_insert_powers
-- name    : PauliUnclonable531.Pauli.insert_powers
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-08T11:09:27.349263+00:00
-- url     : https://prove2.me/theorems/de591801-28e7-4ddf-8b5f-358718a71811
-- title:
--   Proposition 4.6 — inserting every nonnegative agreement power
-- statement:
--   Let n≥1, d=2ⁿ and K=4ⁿ−1. On arbitrary nonzero finite complex registers B,C choose key-indexed Hermitian contractions Bₖ,Cₖ. Set Θₖ=Pₖᵀ and define E_B,E_C,E_BC,D and G by Definition 4.3: E_B and E_C average the reference–receiver tensors, E_BC averages I⊗Bₖ⊗Cₖ, D=I−E_BC, and G=(E_B+E_C−D)/2. Write γ=d/K.
--
--   $$\|E_BE_{BC}^{\ell}E_C\|_\infty\le\|E_BE_C\|_\infty\le\gamma\qquad(\ell\ge0).$$
--
--   The exponent is any natural number, equivalently a nonnegative integer; the case ℓ=0 is included.
--
--   Differences from the source:
--   - encoding: finite-dimensional complex Hilbert-space operators and binary strings → complex matrices indexed by finite computational bases, Fin 2 bits, real Born probabilities, Euclidean spectral norm and PSD-difference order; reason: these are the same finite-dimensional objects and conventions after choosing the source basis
--   - encoding: every integer ℓ≥0 → ℓ : ℕ; reason: natural exponents index exactly the source range
-- source:
--   Prabhanjan Ananth, Seyoon Ragavan, Amit Sahai, STOC 2027 submission #531 (October 2026), Proposition 4.6, p.22, Eq. (31)

import Mathlib
import Definitions.Def_PauliUnclonable531_Pauli_Correlations

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder
set_option autoImplicit false

namespace PauliUnclonable531.Pauli

theorem insert_powers {B C : Type} [Fintype B] [Fintype C] [DecidableEq B] [DecidableEq C]
    [Nonempty B] [Nonempty C] (n : ℕ) (hn : 1 ≤ n) (a : Decoders n B C) (ℓ : ℕ) :
    spectralNorm (EB a * EBC a ^ ℓ * EC a) ≤ spectralNorm (EB a * EC a) ∧
    spectralNorm (EB a * EC a) ≤ gamma n := by sorry

end PauliUnclonable531.Pauli
