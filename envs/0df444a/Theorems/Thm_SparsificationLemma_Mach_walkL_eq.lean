-- Prove2me | Theorems.Thm_SparsificationLemma_Mach_walkL_eq
-- name    : SparsificationLemma.Mach.walkL_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T04:02:19.728343+00:00
-- url     : https://prove2.me/theorems/924cee47-b4c8-456b-8d7d-0580f5e75201
-- title:
--   Mach: walk L eq
-- statement:
--   If the pad has at least 2·(number of leaves) − 1 units and the word of every state of the walk
--   is no longer than the pad, then `walkL` returns the leaves.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Mach/Walk.lean#L130-L137
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Mach/Walk.lean#L130-L137

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Mach_Defs
import Definitions.Def_ClauseBound_Alg_Top
import Definitions.Def_PaddedDescent_F_Top
import Definitions.Def_PaddedDescent_F_Top
import Definitions.Def_SparsificationLemma_Mach_Walk
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.Mach
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSatRate UniformInK PaddedDescent PaddedDescent.F ClauseBound.Alg

theorem SparsificationLemma.Mach.walkL_eq (k : ℕ) (pad : U) (τ : ℕ) (r : CNode) (d : ℕ) (hd : ∀ x ∈ leaves (stepC (thetaU τ) k) d r, stepC (thetaU τ) k x = none)
    (hlen : 2 * (leaves (stepC (thetaU τ) k) d r).length ≤ pad.length + 1) (hst : ∀ i, len ((round (stepC (thetaU τ) k))^[i] ([r], [])) ≤ pad.length) :
    walkL k pad τ r = leaves (stepC (thetaU τ) k) d r := by sorry
