-- Prove2me | Theorems.Thm_VariableBound_Fld_Cert_ipW_polyT
-- name    : VariableBound.Fld.Cert.ipW_polyT
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T23:18:38.816922+00:00
-- url     : https://prove2.me/theorems/f27352dc-1ea2-4518-a0f1-afa795950a00
-- title:
--   Cert: ip W poly T
-- statement:
--   The inner product of two words is polynomial-time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Cert.lean#L79-L80
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Cert.lean#L79-L80

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

theorem VariableBound.Fld.Cert.ipW_polyT {x y : α → List Bool} (hx : PolyT x) (hy : PolyT y) : PolyT fun c => ipW (x c) (y c) := by sorry
