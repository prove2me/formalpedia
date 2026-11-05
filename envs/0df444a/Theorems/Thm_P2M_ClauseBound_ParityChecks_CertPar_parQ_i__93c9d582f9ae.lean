-- Prove2me | Theorems.Thm_P2M_ClauseBound_ParityChecks_CertPar_parQ_i__93c9d582f9ae
-- name    : P2M_ClauseBound_ParityChecks_CertPar_parQ_i__93c9d582f9ae
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:21:03.270774+00:00
-- url     : https://prove2.me/theorems/1840fb13-bf86-4062-8924-e70087e7ea9d
-- title:
--   P2 M Clause Bound Parity Checks Cert Par par Q i  93c9d582f9ae: P2 M Clause Bound Parity Checks Cert Par par Q i  93c9d582f9ae
-- statement:
--   The fourth parameter is i₀.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertPar.lean#L63-L63
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertPar.lean#L63-L63

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

theorem P2M_ClauseBound_ParityChecks_CertPar_parQ_i__93c9d582f9ae (n Δ m : ℕ) : (parQ n Δ m).i₀ = i0Of n := by sorry

alias «ClauseBound».«ParityChecks».«CertPar».«parQ_i₀» := P2M_ClauseBound_ParityChecks_CertPar_parQ_i__93c9d582f9ae
