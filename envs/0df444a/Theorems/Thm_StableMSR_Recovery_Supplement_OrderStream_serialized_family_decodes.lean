-- Prove2me | Theorems.Thm_StableMSR_Recovery_Supplement_OrderStream_serialized_family_decodes
-- name    : StableMSR.Recovery.Supplement.OrderStream.serialized_family_decodes
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-20T18:01:30.025176+00:00
-- url     : https://prove2.me/theorems/3eda2c05-c77d-4c55-b3fd-3a87c90dfc52
-- title:
--   The charged output format decodes the intended family
-- statement:
--   The first cell gives the number of permutations. Each subsequent record has length m and entries in increasing rank, so the public decoder traverses exactly the intended records.
-- source:
--   Shyam Ravichandran and Lev Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, arXiv:2611.03547, Appendix B, Theorem B.2. Charged deterministic RAM implementation.

import Definitions.Def_StableMSR_PolynomialOrderStream
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.Compiler.BoundedSum
open Polynomial
open StableMSR.Recovery.Supplement StableMSR.Recovery.Supplement.OrderStream

theorem StableMSR.Recovery.Supplement.OrderStream.serialized_family_decodes (m : ℕ) (s : MinSumFPT.State) (h : ∀j<span m,s.imem (-1-(j:ℤ))=(word m j:ℤ)) :
    MinSumFPT.outputSets s=family m := by
  sorry
