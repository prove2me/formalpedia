-- Prove2me | Theorems.Thm_VariableBound_Rename_rencC_encC
-- name    : VariableBound.Rename.rencC_encC
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:57:23.341278+00:00
-- url     : https://prove2.me/theorems/cb38ee8f-6ef3-470c-87ac-1819a2b21dd8
-- title:
--   Rename: renc C enc C
-- statement:
--   The front end maps the compact code of (k, φ) to the code of (k, φ renamed), for k ≥ 1 and φ
--   with at most k literals in every clause.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Rename/Compact.lean#L74-L76
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Rename/Compact.lean#L74-L76

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Paper_Rename_Math
import Definitions.Def_VariableBound_Paper_Rename_Code
import Definitions.Def_VariableBound_Paper_Rename_Cert
import Definitions.Def_ClauseBound_Alg_Decode
import Definitions.Def_WidthK_Decode
import Definitions.Def_VariableBound_Paper_Rename_Compact
import Theorems.Thm_Groundwork_DecodeK_decK_enc
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open VariableBound VariableBound.Rename
open Groundwork Groundwork.Prog Groundwork.Decode PaddedDescent.F ClauseBound.Alg MainTheoremForms
open Groundwork.DecodeK (clauseDec decK decK_enc)
open Sat3 (CNF)

theorem VariableBound.Rename.rencC_encC {k N : ℕ} (φ : CNF N) (hk : 1 ≤ k) (hφ : ∀ C ∈ φ, C.length ≤ k) : rencC (encC k φ) = SatM.enc k (ren φ) := by sorry
