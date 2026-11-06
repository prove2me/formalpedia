-- Prove2me | Theorems.Thm_VariableBound_Fld_Cert_powW_polyT
-- name    : VariableBound.Fld.Cert.powW_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:31:57.397137+00:00
-- url     : https://prove2.me/theorems/2fecdb35-0cfb-4df6-8df9-9949756b328e
-- title:
--   Cert: pow W poly T
-- statement:
--   Powers are polynomial-time, if the exponent is given in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Cert.lean#L95-L102
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Cert.lean#L95-L102

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

theorem VariableBound.Fld.Cert.powW_polyT {g u : α → List Bool} {e : α → ℕ} (hg : PolyT g) (hu : PolyT u) (he : Unary e) : PolyT fun c => powW (g c) (u c) (e c) := by sorry
