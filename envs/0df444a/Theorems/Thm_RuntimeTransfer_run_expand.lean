-- Prove2me | Theorems.Thm_RuntimeTransfer_run_expand
-- name    : RuntimeTransfer.run_expand
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T11:20:22.243199+00:00
-- url     : https://prove2.me/theorems/50e24200-cad5-4b96-846a-dc3f4f5c528b
-- title:
--   Exact composition of oracle reductions
-- statement:
--   For any outer program, any assignment of an inner oracle program to each outer query, and any inner costed oracle, running the expanded outer program yields exactly the same answer/cost pair as running the outer program with the oracle that executes each inner program and returns its full answer/cost pair. No extra dispatch cost is added by the accounting semantics.
-- source:
--   General runtime transfer and its Fourier/packing applications, companion proof note for this mission, 24 October 2026. Original cost-semantics formulation of standard substitution principles; not a claimed new complexity bound. Theorem 2.

import Definitions.Def_RuntimeTransfer
set_option autoImplicit false
open RuntimeTransfer

theorem RuntimeTransfer.run_expand {Q A R Q' A' : Type} (p : Program Q A R)
    (inner : Q → Program Q' A' A) (oracle : Q' → A' × ℕ) :
    (p.expand inner).run oracle = p.run (fun q => (inner q).run oracle) := by sorry
