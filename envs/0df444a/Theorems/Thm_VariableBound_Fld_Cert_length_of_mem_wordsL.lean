-- Prove2me | Theorems.Thm_VariableBound_Fld_Cert_length_of_mem_wordsL
-- name    : VariableBound.Fld.Cert.length_of_mem_wordsL
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:42:41.668598+00:00
-- url     : https://prove2.me/theorems/036a0359-5b2e-4605-999d-b2b3e87c2974
-- title:
--   Cert: length of mem words L
-- statement:
--   Every word in the list of the words of s bits has s bits.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Cert.lean#L126-L128
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Cert.lean#L126-L128

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Field_Defs
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ClauseBound_ParityChecks_CertLib
import Mathlib.Data.List.Find
import Definitions.Def_VariableBound_Field_Cert
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open VariableBound VariableBound.Fld VariableBound.Fld.Cert
open Groundwork PaddedDescent.F ClauseBound.ParityChecks.CertLib
variable {α : Type} [Enc α]

theorem VariableBound.Fld.Cert.length_of_mem_wordsL {s : ℕ} {g : List Bool} (h : g ∈ wordsL s) : g.length = s := by sorry
