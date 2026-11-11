-- Prove2me | Theorems.Thm_PauliUnclonable531_Pauli_filter_properties
-- name    : PauliUnclonable531.Pauli.filter_properties
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-08T11:08:23.092947+00:00
-- url     : https://prove2.me/theorems/56a03663-f5d6-4da2-8c8a-43e67b4c82a4
-- title:
--   Definition 4.7 — positive filter and both inverse cancellations
-- statement:
--   Let n≥1, d=2ⁿ and K=4ⁿ−1. On arbitrary nonzero finite complex registers B,C choose key-indexed Hermitian contractions Bₖ,Cₖ. Set Θₖ=Pₖᵀ and define E_B,E_C,E_BC,D and G by Definition 4.3: E_B and E_C average the reference–receiver tensors, E_BC averages I⊗Bₖ⊗Cₖ, D=I−E_BC, and G=(E_B+E_C−D)/2. Write γ=d/K.
--
--   For every positive real t define F(t)=2t(2tI+D)⁻¹. Then
--
--   $$2tI+D\succ0,\quad0\prec F(t)\preceq I,\quad(2tI+D)F(t)=F(t)(2tI+D)=2tI.$$
--
--   These are the defining filter properties and identities recorded on p.23. Positive definiteness ensures that the total matrix inverse used by Lean is the genuine inverse, including when D has a kernel.
--
--   Differences from the source:
--   - encoding: finite-dimensional complex Hilbert-space operators and binary strings → complex matrices indexed by finite computational bases, Fin 2 bits, real Born probabilities, Euclidean spectral norm and PSD-difference order; reason: these are the same finite-dimensional objects and conventions after choosing the source basis
-- source:
--   Prabhanjan Ananth, Seyoon Ragavan, Amit Sahai, STOC 2027 submission #531 (October 2026), Definition 4.7, p.23, Eqs. (33)–(34)

import Mathlib
import Definitions.Def_PauliUnclonable531_Pauli_Correlations

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder
set_option autoImplicit false

namespace PauliUnclonable531.Pauli

/-- Definition 4.7 and Eq. (34), p.23: the inverse is genuine even when D is singular. -/
theorem filter_properties {B C : Type} [Fintype B] [Fintype C] [DecidableEq B] [DecidableEq C]
    [Nonempty B] [Nonempty C] (n : ℕ) (hn : 1 ≤ n) (a : Decoders n B C) (t : ℝ) (ht : 0 < t) :
    ((2 * (t : ℂ)) • (1 : Op (Bits n × (B × C))) + disagreement a).PosDef ∧
    (filterOperator a t).PosDef ∧ Below (filterOperator a t) 1 ∧
    (((2 * (t : ℂ)) • 1 + disagreement a) * filterOperator a t = (2 * (t : ℂ)) • 1) ∧
    (filterOperator a t * ((2 * (t : ℂ)) • 1 + disagreement a) = (2 * (t : ℂ)) • 1) := by sorry

end PauliUnclonable531.Pauli
