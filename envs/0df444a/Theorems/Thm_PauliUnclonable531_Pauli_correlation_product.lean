-- Prove2me | Theorems.Thm_PauliUnclonable531_Pauli_correlation_product
-- name    : PauliUnclonable531.Pauli.correlation_product
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-08T11:08:20.517634+00:00
-- url     : https://prove2.me/theorems/dfc1be3a-9655-4b7f-95b5-dc0bb2c996ea
-- title:
--   Lemma 4.4 — product of correlation operators
-- statement:
--   Let n≥1, d=2ⁿ and K=4ⁿ−1. On arbitrary nonzero finite complex registers B,C choose key-indexed Hermitian contractions Bₖ,Cₖ. Set Θₖ=Pₖᵀ and define E_B,E_C,E_BC,D and G by Definition 4.3: E_B and E_C average the reference–receiver tensors, E_BC averages I⊗Bₖ⊗Cₖ, D=I−E_BC, and G=(E_B+E_C−D)/2. Write γ=d/K.
--
--   $$\|E_BE_C\|_\infty\le\gamma.$$
--
--   The estimate applies to arbitrary Hermitian contractions, without a channel or a projectivity restriction.
--
--   Differences from the source:
--   - encoding: finite-dimensional complex Hilbert-space operators and binary strings → complex matrices indexed by finite computational bases, Fin 2 bits, real Born probabilities, Euclidean spectral norm and PSD-difference order; reason: these are the same finite-dimensional objects and conventions after choosing the source basis
-- source:
--   Prabhanjan Ananth, Seyoon Ragavan, Amit Sahai, STOC 2027 submission #531 (October 2026), Lemma 4.4, p.19, Eq. (30)

import Mathlib
import Definitions.Def_PauliUnclonable531_Pauli_Correlations

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder
set_option autoImplicit false

namespace PauliUnclonable531.Pauli

theorem correlation_product {B C : Type} [Fintype B] [Fintype C] [DecidableEq B] [DecidableEq C]
    [Nonempty B] [Nonempty C] (n : ℕ) (hn : 1 ≤ n) (a : Decoders n B C) :
    spectralNorm (EB a * EC a) ≤ gamma n := by sorry

end PauliUnclonable531.Pauli
