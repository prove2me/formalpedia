-- Prove2me | Theorems.Thm_VariableBound_Fld_Cert_mulW_polyT
-- name    : VariableBound.Fld.Cert.mulW_polyT
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T23:29:44.796441+00:00
-- url     : https://prove2.me/theorems/2eaace86-7afc-4292-a0a7-fbe872b8cf7c
-- title:
--   Cert: mul W poly T
-- statement:
--   Multiplication is polynomial-time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Cert.lean#L83-L92
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Cert.lean#L83-L92

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

theorem VariableBound.Fld.Cert.mulW_polyT {g x y : α → List Bool} (hg : PolyT g) (hx : PolyT x) (hy : PolyT y) : PolyT fun c => mulW (g c) (x c) (y c) := by sorry
