-- Prove2me | Theorems.Thm_StableMSR_Recovery_Supplement_OrderStream_hash_order_stream_is_bounded
-- name    : StableMSR.Recovery.Supplement.OrderStream.hash_order_stream_is_bounded
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-20T18:01:30.860208+00:00
-- url     : https://prove2.me/theorems/8d74019e-98f4-4d4e-9b57-d51a34dd6a03
-- title:
--   Hash-order output entries have bounded-sum expressions
-- statement:
--   Use bounded divisor tests for primality, fixed powers for coefficient extraction and polynomial evaluation, and counts of smaller keys to compute ranks. Address arithmetic supplies the length fields and entries of the serialized output.
-- source:
--   Shyam Ravichandran and Lev Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, arXiv:2611.03547, Appendix B, Theorem B.2. Charged deterministic RAM implementation.

import Definitions.Def_StableMSR_PolynomialOrderStream
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.Compiler.BoundedSum
open Polynomial
open StableMSR.Recovery.Supplement StableMSR.Recovery.Supplement.OrderStream

theorem StableMSR.Recovery.Supplement.OrderStream.hash_order_stream_is_bounded : Form (fun ρ=>span (ρ 0)) ∧ Form (fun ρ=>word (ρ 0) (ρ 1)) := by
  sorry
