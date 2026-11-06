-- Prove2me | Theorems.Thm_VariableBound_Fld_Cert_gamW_polyT
-- name    : VariableBound.Fld.Cert.gamW_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:43:29.936206+00:00
-- url     : https://prove2.me/theorems/f71529d1-9a99-4b76-9705-f6db4faafd30
-- title:
--   Cert: gam W poly T
-- statement:
--   The set Γ_u is polynomial-time jointly in m, a, g and u, if m is given in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Cert.lean#L144-L154
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Cert.lean#L144-L154

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

theorem VariableBound.Fld.Cert.gamW_polyT {m a : α → ℕ} {g : α → List Bool} {u : α → List Bool × List Bool × List Bool × List Bool} (hm : Unary m) (ha : PolyT a) (hg : PolyT g) (hu : PolyT u) :
    PolyT fun c => gamW (m c) (a c) (g c) (u c) := by sorry
