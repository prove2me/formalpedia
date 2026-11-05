-- Prove2me | Theorems.Thm_VariableBound_Fld_Cert_zeroW_polyT
-- name    : VariableBound.Fld.Cert.zeroW_polyT
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T23:13:30.661488+00:00
-- url     : https://prove2.me/theorems/b2fde734-ec9e-4b78-bc08-8366540c1c18
-- title:
--   Cert: zero W poly T
-- statement:
--   The word 0 of the length of g is polynomial-time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Cert.lean#L67-L68
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Cert.lean#L67-L68

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

theorem VariableBound.Fld.Cert.zeroW_polyT {g : α → List Bool} (hg : PolyT g) : PolyT fun c => zeroW (g c) := by sorry
