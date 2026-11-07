-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_productExpanding_mono
-- name    : QEC.Coding.ProductExpansion.productExpanding_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:56:34.075487+00:00
-- url     : https://prove2.me/theorems/3e50ee71-69d7-4b74-8258-bc316e34d20d
-- title:
--   Product Expansion: product Expanding mono
-- statement:
--   Expansion persists under weaker output and rectangle bounds and stricter minimality.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L640-L652
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L640-L652

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

theorem QEC.Coding.ProductExpansion.productExpanding_mono
    (h : Matrix R W F) (h' : Matrix R' W F)
    {s s' m m' : Nat} {beta beta' : ℝ}
    (hExpand : ProductExpanding h h' s m beta)
    (hs : s' ≤ s) (hm : m' ≤ m) (hbeta : beta' ≤ beta) :
    ProductExpanding h h' s' m' beta' := by sorry
