-- Prove2me | Theorems.Thm_VariableBound_Rename_renc_enc
-- name    : VariableBound.Rename.renc_enc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:28:22.737494+00:00
-- url     : https://prove2.me/theorems/f540eb21-4101-43cc-b52f-ce525142b234
-- title:
--   Rename: renc enc
-- statement:
--   The front end maps the code of (k, φ) to the code of (k, φ renamed), for k ≥ 1 and φ with at
--   most k literals in every clause.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Rename/Code.lean#L35-L37
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Rename/Code.lean#L35-L37

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Paper_Rename_Math
import Definitions.Def_ClauseBound_Alg_Decode
import Definitions.Def_VariableBound_Paper_Rename_Code
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open VariableBound VariableBound.Rename
open Groundwork Groundwork.Prog Groundwork.Decode PaddedDescent.F ClauseBound.Alg MainTheoremForms
open Sat3 (CNF)

theorem VariableBound.Rename.renc_enc {k N : ℕ} (φ : CNF N) (hk : 1 ≤ k) (hφ : ∀ C ∈ φ, C.length ≤ k) : renc (SatM.enc k φ) = SatM.enc k (ren φ) := by sorry
