-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_codeword_eq_zero_of_minimality_and_complement_bound
-- name    : QEC.Coding.ProductExpansion.codeword_eq_zero_of_minimality_and_complement_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:30:31.042522+00:00
-- url     : https://prove2.me/theorems/ffb1c6be-9cb8-4e20-bac8-44cc90bedbea
-- title:
--   Product Expansion: codeword eq zero of minimality and complement bound
-- statement:
--   The numerical core of the nonzero-block proof: a nonzero local codeword
--   cannot be a near-minimal correction when the residual word is supported outside
--   a sufficiently large coordinate set.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L351-L371
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L351-L371

import Definitions.Def_QEC_Coding_Core_Definitions
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [Fintype R] [Fintype R']
omit [Fintype R] [Fintype R']

theorem QEC.Coding.ProductExpansion.codeword_eq_zero_of_minimality_and_complement_bound
    (h : Matrix R W F) (d : Nat)
    (hDistance : ∀ c : Word F W, c ∈ (parityCheckCode h).carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (A : Finset W) (delta : ℝ)
    (hGap : 2 * (Fintype.card W - A.card : ℝ) + delta < d)
    (x c : Word F W) (hc : c ∈ (parityCheckCode h).carrier)
    (hCorrected : ∀ j ∈ A, (x - c) j = 0)
    (hMinimal : (HammingWeight x : ℝ) ≤ HammingWeight (x - c) + delta) :
    c = 0 := by sorry
