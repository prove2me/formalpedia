-- Prove2me | Theorems.Thm_QEC_Coding_SmallSetExpansion_sum_mul_le_of_dyadic_mixing
-- name    : QEC.Coding.SmallSetExpansion.sum_mul_le_of_dyadic_mixing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:37:25.200194+00:00
-- url     : https://prove2.me/theorems/1f559ccd-b7c3-4ce6-8da0-2b604da6784f
-- title:
--   Small Set Expansion: sum mul le of dyadic mixing
-- statement:
--   Dyadic form of the PK22 intermediate-vertex count.  If every subset of
--   `U` has both `p`- and `q`-mass bounded by the two mixing estimates, and
--   `1 ≤ p x ≤ degree` on `U`, then the sum of `p x * q x` loses only the number
--   of dyadic degree levels.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/SmallSetExpansionSquare.lean#L588-L701
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/SmallSetExpansionSquare.lean#L588-L701

import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansion
import Mathlib.Data.Nat.Log
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u}

theorem QEC.Coding.SmallSetExpansion.sum_mul_le_of_dyadic_mixing
    [Fintype V] [DecidableEq V]
    (p q : V → Nat) (U : Finset V) (degree : Nat) (lambda : ℝ)
    (sCard tCard : Nat)
    (hLambda : 0 ≤ lambda)
    (hPPos : ∀ x ∈ U, 0 < p x)
    (hPBound : ∀ x ∈ U, p x ≤ degree)
    (hPMix : ∀ A : Finset V, A ⊆ U →
      (∑ x ∈ A, (p x : ℝ)) ≤
        lambda * Real.sqrt ((A.card : ℝ) * sCard))
    (hQMix : ∀ A : Finset V, A ⊆ U →
      (∑ x ∈ A, (q x : ℝ)) ≤
        lambda * Real.sqrt ((A.card : ℝ) * tCard)) :
    (∑ x ∈ U, ((p x * q x : Nat) : ℝ)) ≤
      ((Nat.log 2 degree + 1 : Nat) : ℝ) *
        (2 * lambda ^ 2 * Real.sqrt ((sCard : ℝ) * tCard)) := by sorry
