-- Prove2me | Theorems.Thm_VariableBound_Fld_Cert_wordsL_polyT
-- name    : VariableBound.Fld.Cert.wordsL_polyT
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T00:51:53.883763+00:00
-- url     : https://prove2.me/theorems/1614b256-6b46-461b-b5e0-8485ec15e72e
-- title:
--   Cert: words L poly T
-- statement:
--   The list of all words of s bits is polynomial-time, if s and 2^s are given in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Cert.lean#L107-L111
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Cert.lean#L107-L111

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Field_Defs
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ClauseBound_ParityChecks_CertLib
import Mathlib.Data.List.Find
import Definitions.Def_VariableBound_Field_Cert
set_option autoImplicit false
section
section
open VariableBound VariableBound.Fld VariableBound.Fld.Cert
open Groundwork PaddedDescent.F ClauseBound.ParityChecks.CertLib
variable {α : Type} [Enc α]

theorem VariableBound.Fld.Cert.wordsL_polyT {s : α → ℕ} (hs : Unary s) (h2 : Unary fun c => 2 ^ s c) : PolyT fun c => wordsL (s c) := by sorry
