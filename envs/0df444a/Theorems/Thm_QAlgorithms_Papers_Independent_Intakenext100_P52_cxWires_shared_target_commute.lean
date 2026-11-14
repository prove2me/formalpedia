-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P52_cxWires_shared_target_commute
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P52.cxWires_shared_target_commute
-- status  : Proved
-- author  : @Mrnaiq
-- created : 2026-11-14T04:39:13.074768+00:00
-- url     : https://prove2.me/theorems/3bcda4ae-d01b-4235-86f6-eb866309a1bf
-- title:
--   Controlled bit flips with a common target commute
-- statement:
--   Let $V$ be a finite set of qubit wires. Let $a,b,t\in V$, with $a\ne t$ and $b\ne t$. Write $CX_{a\to t}$ for the controlled bit flip that replaces the target bit $z_t$ by $z_t\oplus z_a$ and leaves every other bit unchanged. Then, as matrices on the full computational register,
--
--   $$CX_{a\to t}\,CX_{b\to t}=CX_{b\to t}\,CX_{a\to t}.$$
--
--   The two controls may coincide. This circuit identity justifies reordering the entangling gates in the Bell-measurement decomposition of teleportation.
-- source:
--   R. Jozsa, An introduction to measurement based quantum computation, https://arxiv.org/abs/quant-ph/0508124v2, PDF pp.15–16, Figure 12 and its caption; general finite-wire form of the shared-target commutation identity.

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P52
noncomputable section
open QAlgorithms QAlgorithms.Papers.Independent.Intakenext100.P52
set_option autoImplicit false

theorem QAlgorithms.Papers.Independent.Intakenext100.P52.cxWires_shared_target_commute {V : Type*} [Fintype V] [DecidableEq V]
    (a b t : V) (ha : a ≠ t) (hb : b ≠ t) :
    cxWires a t * cxWires b t = cxWires b t * cxWires a t := by sorry
