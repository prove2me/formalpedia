-- Prove2me | Theorems.Thm_P2M_ClauseBound_ParityChecks_CertPar_parQ___e24fc9b201b1
-- name    : P2M_ClauseBound_ParityChecks_CertPar_parQ___e24fc9b201b1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:18:59.426439+00:00
-- url     : https://prove2.me/theorems/d03f1fde-62f5-4c60-812c-85d9b4c5ea10
-- title:
--   P2 M Clause Bound Parity Checks Cert Par par Q   e24fc9b201b1: P2 M Clause Bound Parity Checks Cert Par par Q   e24fc9b201b1
-- statement:
--   The fifth parameter is n + β₀ + β₁ + 2.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertPar.lean#L65-L65
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertPar.lean#L65-L65

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_ClauseBound_ParityChecks_CertLib
import Definitions.Def_PaddedDescent_F_CertMark
import Definitions.Def_ClauseBound_ParityChecks_CertPar
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.CertPar
open Groundwork PaddedDescent.F ClauseBound.ParityChecks.CertLib
variable {α : Type} [Enc α]

theorem P2M_ClauseBound_ParityChecks_CertPar_parQ___e24fc9b201b1 (n Δ m : ℕ) : (parQ n Δ m).β = n + beta0 m (nbOf n Δ) + beta1 m (i0Of n) + 2 := by sorry

alias «ClauseBound».«ParityChecks».«CertPar».«parQ_β» := P2M_ClauseBound_ParityChecks_CertPar_parQ___e24fc9b201b1
