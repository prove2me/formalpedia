-- Prove2me | Theorems.Thm_SparsificationLemma_Mach_Cert_polyT_codeP
-- name    : SparsificationLemma.Mach.Cert.polyT_codeP
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:01:22.307407+00:00
-- url     : https://prove2.me/theorems/412fc46e-4ba4-460f-82e5-38c98bd82dbd
-- title:
--   Cert: poly T code P
-- statement:
--   The code of a list of formulas, cut off, is polynomial-time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Mach/Cert.lean#L74-L76
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Mach/Cert.lean#L74-L76

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

theorem SparsificationLemma.Mach.Cert.polyT_codeP {pad : α → U} {L : α → List PFml} (hp : PolyT pad) (hL : PolyT L) : PolyT fun x => codeP (pad x) (L x) := by sorry
