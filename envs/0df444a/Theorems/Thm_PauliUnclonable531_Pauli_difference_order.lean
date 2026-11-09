-- Prove2me | Theorems.Thm_PauliUnclonable531_Pauli_difference_order
-- name    : PauliUnclonable531.Pauli.difference_order
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:08:30.71693+00:00
-- url     : https://prove2.me/theorems/ee636e84-5434-4520-87f0-cc18e0e7e45c
-- title:
--   Proposition 4.10 — both Loewner difference inequalities
-- statement:
--   Let n≥1, d=2ⁿ and K=4ⁿ−1. On arbitrary nonzero finite complex registers B,C choose key-indexed Hermitian contractions Bₖ,Cₖ. Set Θₖ=Pₖᵀ and define E_B,E_C,E_BC,D and G by Definition 4.3: E_B and E_C average the reference–receiver tensors, E_BC averages I⊗Bₖ⊗Cₖ, D=I−E_BC, and G=(E_B+E_C−D)/2. Write γ=d/K.
--
--   $$-D\preceq E_B-E_C\preceq D.$$
--
--   Both directions of the order bound are retained, on the actual averaged operators.
--
--   Differences from the source:
--   - encoding: finite-dimensional complex Hilbert-space operators and binary strings → complex matrices indexed by finite computational bases, Fin 2 bits, real Born probabilities, Euclidean spectral norm and PSD-difference order; reason: these are the same finite-dimensional objects and conventions after choosing the source basis
-- source:
--   Prabhanjan Ananth, Seyoon Ragavan, Amit Sahai, STOC 2027 submission #531 (October 2026), Proposition 4.10, p.25, Eq. (38)

import Mathlib
import Definitions.Def_PauliUnclonable531_Pauli_Correlations

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder
set_option autoImplicit false

namespace PauliUnclonable531.Pauli

theorem difference_order {B C : Type} [Fintype B] [Fintype C] [DecidableEq B] [DecidableEq C]
    [Nonempty B] [Nonempty C] (n : ℕ) (hn : 1 ≤ n) (a : Decoders n B C) :
    Below (-disagreement a) (EB a - EC a) ∧ Below (EB a - EC a) (disagreement a) := by sorry

end PauliUnclonable531.Pauli
