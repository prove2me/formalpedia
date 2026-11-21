-- Prove2me | Theorems.Thm_StableMSR_Recovery_OracleQueries_point_output_loop
-- name    : StableMSR.Recovery.OracleQueries.point_output_loop
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-20T20:23:05.940633+00:00
-- url     : https://prove2.me/theorems/44596388-14f1-43f7-bf41-088650f8e7d1
-- title:
--   Write the labels of a bounded distance-oracle query
-- statement:
--   One finite command evaluates a fixed expression at every input point and writes the resulting integer labels in the public output format, leaving the input table available throughout.
-- source:
--   Shyam Ravichandran and Lev Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, arXiv:2611.03547, Algorithm 1 and Theorem 1.1. Finite deterministic RAM implementation and ball-cover certification.

import Definitions.Def_StableMSR_OracleQueries
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open Polynomial

theorem StableMSR.Recovery.OracleQueries.point_output_loop (f : World→ℕ→ℤ) (h : Form (fun x ρ=>iv (f x (ρ 0)))) :
    ∃ p : Polynomial ℕ, ∃cmd : Cmd,∀ (x : World) (s : Store),Ready x s →
    ∃t z,Executes x.dist cmd s t z ∧ z ≤ p.eval x.cap ∧
      ∀i < x.n,t.imem (-1-(i:ℤ))=f x i := by
  sorry
