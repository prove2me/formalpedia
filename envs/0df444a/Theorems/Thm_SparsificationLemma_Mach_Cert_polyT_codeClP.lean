-- Prove2me | Theorems.Thm_SparsificationLemma_Mach_Cert_polyT_codeClP
-- name    : SparsificationLemma.Mach.Cert.polyT_codeClP
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T04:03:17.861881+00:00
-- url     : https://prove2.me/theorems/4954c1bc-b6cb-4a79-8c4e-83bbc37024b8
-- title:
--   Cert: poly T code Cl P
-- statement:
--   The code of a clause, cut off, is polynomial-time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Mach/Cert.lean#L64-L66
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Mach/Cert.lean#L64-L66

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

theorem SparsificationLemma.Mach.Cert.polyT_codeClP {pad : α → U} {C : α → PCl} (hp : PolyT pad) (hC : PolyT C) : PolyT fun x => codeClP (pad x) (C x) := by sorry
