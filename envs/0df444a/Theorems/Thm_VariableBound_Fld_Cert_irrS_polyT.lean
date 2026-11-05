-- Prove2me | Theorems.Thm_VariableBound_Fld_Cert_irrS_polyT
-- name    : VariableBound.Fld.Cert.irrS_polyT
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:42:46.738532+00:00
-- url     : https://prove2.me/theorems/1f4746e2-1252-4de6-b07c-51e9b2f5fd0a
-- title:
--   Cert: irr S poly T
-- statement:
--   The test with the number s of bits as an argument is polynomial-time, if s and 2^s are given in
--   unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Cert.lean#L119-L123
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Cert.lean#L119-L123

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

theorem VariableBound.Fld.Cert.irrS_polyT {s : α → ℕ} {g : α → List Bool} (hs : Unary s) (h2 : Unary fun c => 2 ^ s c) (hg : PolyT g) : PolyT fun c => irrS (s c) (g c) := by sorry
