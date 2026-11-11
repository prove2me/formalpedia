-- Prove2me | Theorems.Thm_PauliUnclonable531_Pauli_quadratic_sandwich
-- name    : PauliUnclonable531.Pauli.quadratic_sandwich
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-08T11:08:47.407835+00:00
-- url     : https://prove2.me/theorems/d34f2163-05e0-4c11-964b-46fd86edd21e
-- title:
--   Proposition 4.11 — quadratic sandwich bound
-- statement:
--   Let n≥1, d=2ⁿ and K=4ⁿ−1. On arbitrary nonzero finite complex registers B,C choose key-indexed Hermitian contractions Bₖ,Cₖ. Set Θₖ=Pₖᵀ and define E_B,E_C,E_BC,D and G by Definition 4.3: E_B and E_C average the reference–receiver tensors, E_BC averages I⊗Bₖ⊗Cₖ, D=I−E_BC, and G=(E_B+E_C−D)/2. Write γ=d/K.
--
--   $$(E_B-E_C)F(t)(E_B-E_C)\preceq2tD\qquad(t>0).$$
--
--   The bound holds for every positive real t and includes singular D.
--
--   Differences from the source:
--   - encoding: finite-dimensional complex Hilbert-space operators and binary strings → complex matrices indexed by finite computational bases, Fin 2 bits, real Born probabilities, Euclidean spectral norm and PSD-difference order; reason: these are the same finite-dimensional objects and conventions after choosing the source basis
-- source:
--   Prabhanjan Ananth, Seyoon Ragavan, Amit Sahai, STOC 2027 submission #531 (October 2026), Proposition 4.11, p.25

import Mathlib
import Definitions.Def_PauliUnclonable531_Pauli_Correlations

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder
set_option autoImplicit false

namespace PauliUnclonable531.Pauli

theorem quadratic_sandwich {B C : Type} [Fintype B] [Fintype C] [DecidableEq B] [DecidableEq C]
    [Nonempty B] [Nonempty C] (n : ℕ) (hn : 1 ≤ n) (a : Decoders n B C) (t : ℝ) (ht : 0 < t) :
    Below ((EB a - EC a) * filterOperator a t * (EB a - EC a))
      ((2 * (t : ℂ)) • disagreement a) := by sorry

end PauliUnclonable531.Pauli
