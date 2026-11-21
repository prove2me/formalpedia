-- Prove2me | Theorems.Thm_StableMSR_Recovery_OracleQueries_axis_sum_machine
-- name    : StableMSR.Recovery.OracleQueries.axis_sum_machine
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-20T20:23:02.691016+00:00
-- url     : https://prove2.me/theorems/8eba4342-9ae7-4c43-bf60-3c9dcfc45bc9
-- title:
--   Charge an oracle sum over points, blocks, or rows
-- statement:
--   A bounded scan simultaneously sums the integer and real components of its body, preserving its input registers and integer table. The running time is polynomial in the axis sizes.
-- source:
--   Shyam Ravichandran and Lev Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, arXiv:2611.03547, Algorithm 1 and Theorem 1.1. Finite deterministic RAM implementation and ball-cover certification.

import Definitions.Def_StableMSR_OracleQueries
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open Polynomial

theorem StableMSR.Recovery.OracleQueries.axis_sum_machine (a : Axis) (f : Term) (h : Engine f) :
    Engine (fun x ρ=>∑i ∈ Finset.range (x.size a), f x (push i ρ)) := by
  sorry
