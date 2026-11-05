-- Prove2me | Theorems.Thm_PaddedDescent_F_CertNet_rebalG_polyT
-- name    : PaddedDescent.F.CertNet.rebalG_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:18:11.292951+00:00
-- url     : https://prove2.me/theorems/27d2f90a-2c3e-465e-80e0-e2d077dc3b10
-- title:
--   Cert Net: rebal G poly T
-- statement:
--   `rebalG` is polynomial-time, jointly in the pad, in K, g and the label length (in unary), and in
--   the context.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Col/CertG.lean#L45-L61
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Col/CertG.lean#L45-L61

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_CertNet
import Definitions.Def_PaddedDescent_Col_CertG
set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.CertNet
open Groundwork Groundwork.Prog Groundwork.Prog.NetE PaddedDescent.F
variable {α : Type} [Enc α] {C : Type} [Enc C] {Np : PNet C}

theorem PaddedDescent.F.CertNet.rebalG_polyT {F : FNet C} (hF : FKeeps F) {pad : α → U} {K g b : α → ℕ} {c : α → C} (hp : PolyT pad) (hK : Unary K)
    (hg : Unary g) (hb : Unary b) (hc : PolyT c) : PolyT fun t => rebalG (pad t) (K t) (g t) (b t) F (c t) := by sorry
