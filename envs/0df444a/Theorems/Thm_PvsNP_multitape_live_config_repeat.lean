-- Prove2me | Theorems.Thm_PvsNP_multitape_live_config_repeat
-- name    : PvsNP.multitape_live_config_repeat
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T10:06:47.157923+00:00
-- url     : https://prove2.me/theorems/e2155e29-4098-43d4-856f-5c78c28252f2
-- title:
--   A repeated live configuration certifies nontermination
-- statement:
--   Fix a deterministic multitape machine and an input. Let $c_j$ be the control state, input head position and complete work-tape configuration after $j$ steps. If $c_u=c_v$ for two times $u<v$ and the machine is still running at time $v$, then its halt flag is false at every time. The output log is write-only and does not form part of $c_j$.
-- source:
--   Deterministic multitape specialization of the loop-closing argument in Biere, Artho and Schuppan, Liveness Checking as Safety Checking (2002), §2, Fig. 1, pp. 2–3, https://fmv.jku.at/papers/BiereArthoSchuppan-FMICS02.pdf.

import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Universal_Basic
import Mathlib
open Turing.MultiTapeTM.Universal

theorem PvsNP.multitape_live_config_repeat (d : Desc) (x : List ℕ) {u v : ℕ} (order : u < v)
    (live : (simulate d x v).2 = false)
    (repeatConfig : ((fun c : SCfg => (step d x c).1)^[u]) (init d) =
      ((fun c : SCfg => (step d x c).1)^[v]) (init d)) :
    ∀ t, (simulate d x t).2 = false := by sorry
