-- Prove2me | Theorems.Thm_VariableBound_Fld_Cert_oneW_polyT
-- name    : VariableBound.Fld.Cert.oneW_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:14:57.132507+00:00
-- url     : https://prove2.me/theorems/294da5f9-24c1-45fc-b087-376648cdedf6
-- title:
--   Cert: one W poly T
-- statement:
--   The word 1 of the length of g is polynomial-time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Cert.lean#L71-L72
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Cert.lean#L71-L72

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

theorem VariableBound.Fld.Cert.oneW_polyT {g : α → List Bool} (hg : PolyT g) : PolyT fun c => oneW (g c) := by sorry
