-- Prove2me | Theorems.Thm_UniformInK_CertWalk_polyT_stepCU
-- name    : UniformInK.CertWalk.polyT_stepCU
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:36:56.277709+00:00
-- url     : https://prove2.me/theorems/882cc067-f089-45fc-916b-0ab70c36b22a
-- title:
--   Cert Walk: poly T step CU
-- statement:
--   The two children of a node of the counting tree are polynomial-time jointly in k, τ and the
--   node, if k and 2^k are given in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Cert/Walk.lean#L30-L34
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Cert/Walk.lean#L30-L34

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInK_Tree_Defs
import Definitions.Def_UniformInK_Cert_Sparsify
import Definitions.Def_CountKSatRate_Cert
import Definitions.Def_UniformInK_Cert_Walk
import Theorems.Thm_CountKSatRate_Cert_polyT_stepCU
attribute [local fun_prop] CountKSatRate.Cert.polyT_stepCU


set_option autoImplicit false
section
section
open UniformInK
open Groundwork Groundwork.Sparsify WidthK.Prog CountKSat CountKSat.Poly PaddedDescent PaddedDescent.F CountKSatRate CountKSatRate.Cert
open UniformInK.CertWalk
variable {α : Type} [Enc α]

theorem UniformInK.CertWalk.polyT_stepCU {k τ : α → ℕ} {s : α → CNode} (hk : Unary k) (h2 : Unary fun x => 2 ^ k x) (hτ : PolyT τ) (hs : PolyT s) :
    PolyT fun x => stepC (thetaU (τ x)) (k x) (s x) := by sorry
