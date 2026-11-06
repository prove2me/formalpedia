-- Prove2me | Theorems.Thm_SparsificationLemma_Mach_Cert_polyT_round
-- name    : SparsificationLemma.Mach.Cert.polyT_round
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:03:00.583149+00:00
-- url     : https://prove2.me/theorems/fe199a2e-0a76-436f-ab93-0f1aaf481f28
-- title:
--   Cert: poly T round
-- statement:
--   One round of the collecting walk is polynomial-time, for a step function that may depend on the
--   context.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Mach/Cert.lean#L42-L44
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Mach/Cert.lean#L42-L44

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Mach_Walk
import Definitions.Def_UniformInK_Cert_Walk
import Definitions.Def_ClauseBound_Alg_Decode
import Definitions.Def_ClauseBound_ParityChecks_CertLib
import Definitions.Def_SparsificationLemma_Mach_Cert
import Theorems.Thm_WidthK_InvK_step

set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.Mach SparsificationLemma.Mach.Cert
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSat.Poly CountKSatRate CountKSatRate.Cert UniformInK PaddedDescent PaddedDescent.F ClauseBound.Alg
variable {α σ : Type} [Enc α]

theorem SparsificationLemma.Mach.Cert.polyT_round [Enc σ] {step : α → σ → Option (σ × σ)} {st : α → List σ × List σ}
    (h1 : PolyT fun p : α × σ => step p.1 p.2) (h3 : PolyT st) : PolyT fun x => Sparsify.round (step x) (st x) := by sorry
