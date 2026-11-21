-- Prove2me | Theorems.Thm_StableMSR_Recovery_Supplement_OrderStream_field_size_spec
-- name    : StableMSR.Recovery.Supplement.OrderStream.field_size_spec
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-20T18:01:57.792637+00:00
-- url     : https://prove2.me/theorems/8ba8bbbf-c209-4091-b5b8-8066b11cef5b
-- title:
--   A deterministically selected quadratic-size prime field
-- statement:
--   Bertrand’s postulate gives a prime between the threshold and twice the threshold. The least such prime is the unique nonzero summand in the field-size definition.
-- source:
--   Shyam Ravichandran and Lev Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, arXiv:2611.03547, Appendix B, Theorem B.2. Charged deterministic RAM implementation.

import Definitions.Def_StableMSR_PolynomialOrderStream
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.Compiler.BoundedSum
open Polynomial
open StableMSR.Recovery.Supplement StableMSR.Recovery.Supplement.OrderStream

theorem StableMSR.Recovery.Supplement.OrderStream.field_size_spec (m : ℕ) : (fieldSize m).Prime ∧ 8193≤fieldSize m ∧ 4*m^2≤fieldSize m ∧ fieldSize m≤2*lower m := by
  sorry
