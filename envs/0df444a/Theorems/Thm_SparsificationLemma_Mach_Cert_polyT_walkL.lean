-- Prove2me | Theorems.Thm_SparsificationLemma_Mach_Cert_polyT_walkL
-- name    : SparsificationLemma.Mach.Cert.polyT_walkL
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:02:31.437298+00:00
-- url     : https://prove2.me/theorems/e8dd1d01-b70c-40e0-a2d7-4c5043942a0f
-- title:
--   Cert: poly T walk L
-- statement:
--   The collecting walk is polynomial-time jointly in k, the pad, τ and the root, if k and 2^k are
--   given in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Mach/Cert.lean#L48-L57
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Mach/Cert.lean#L48-L57

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Mach_Walk
import Definitions.Def_UniformInK_Cert_Walk
import Definitions.Def_ClauseBound_Alg_Decode
import Definitions.Def_ClauseBound_ParityChecks_CertLib
import Definitions.Def_SparsificationLemma_Mach_Cert
set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.Mach SparsificationLemma.Mach.Cert
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSat.Poly CountKSatRate CountKSatRate.Cert UniformInK PaddedDescent PaddedDescent.F ClauseBound.Alg
variable {α σ : Type} [Enc α]

theorem SparsificationLemma.Mach.Cert.polyT_walkL {k : α → ℕ} {pad : α → U} {τ : α → ℕ} {r : α → CNode} (hk : Unary k) (h2 : Unary fun x => 2 ^ k x) (hp : PolyT pad) (hτ : PolyT τ)
    (hr : PolyT r) : PolyT fun t => walkL (k t) (pad t) (τ t) (r t) := by sorry
