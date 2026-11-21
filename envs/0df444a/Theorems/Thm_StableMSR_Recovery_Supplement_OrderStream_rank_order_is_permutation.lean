-- Prove2me | Theorems.Thm_StableMSR_Recovery_Supplement_OrderStream_rank_order_is_permutation
-- name    : StableMSR.Recovery.Supplement.OrderStream.rank_order_is_permutation
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-20T18:03:03.162015+00:00
-- url     : https://prove2.me/theorems/42f2a6c0-64ae-4e1e-9924-9f583859d424
-- title:
--   Ranking distinct hash keys gives the advertised permutation and order
-- statement:
--   Keys consist of a hash value followed by the original vertex index. Their strict ranks give a bijection with the first m naturals. The rank readback is its inverse, so list positions compare exactly as the keys do.
-- source:
--   Shyam Ravichandran and Lev Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, arXiv:2611.03547, Appendix B, Theorem B.2. Charged deterministic RAM implementation.

import Definitions.Def_StableMSR_PolynomialOrderStream
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.Compiler.BoundedSum
open Polynomial
open StableMSR.Recovery.Supplement StableMSR.Recovery.Supplement.OrderStream

theorem StableMSR.Recovery.Supplement.OrderStream.rank_order_is_permutation (m c : ℕ) : (row m c).Perm ((List.range m).map (fun i=>(i:ℤ))) ∧
    ∀ x < m, ∀ y < m, (row m c).idxOf (x:ℤ) < (row m c).idxOf (y:ℤ) ↔ score m c x < score m c y := by
  sorry
