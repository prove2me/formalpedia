-- Prove2me | Theorems.Thm_StableMSR_Recovery_OracleQueries_oracle_query_primitives
-- name    : StableMSR.Recovery.OracleQueries.oracle_query_primitives
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-20T20:23:05.817146+00:00
-- url     : https://prove2.me/theorems/9cf5f316-cf6f-4068-bead-99fefefc39e2
-- title:
--   Register-safe distance and table queries
-- statement:
--   Integer reads, distance queries, comparisons, scalar addition, and conditionals admit charged deterministic implementations that retain the inputs.
-- source:
--   Shyam Ravichandran and Lev Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, arXiv:2611.03547, Algorithm 1 and Theorem 1.1. Finite deterministic RAM implementation and ball-cover certification.

import Definitions.Def_StableMSR_OracleQueries
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open Polynomial

theorem StableMSR.Recovery.OracleQueries.oracle_query_primitives : (∀z : ℤ,Engine (fun _ _=>iv z)) ∧
    (∀i : ℕ,Engine (fun _ ρ=>iv (ρ i))) ∧ (∀a : Axis, Engine (fun x _=>iv (x.size a))) ∧
    (∀ (v : Prim) (f g : Term),Engine f → Engine g → Engine (fun x ρ=>v.val x (f x ρ) (g x ρ))) ∧
    (∀f g h : Term,Engine f → Engine g → Engine h →
      Engine (fun x ρ=>if 1 ≤ (f x ρ).1 then g x ρ else h x ρ)) := by
  sorry
