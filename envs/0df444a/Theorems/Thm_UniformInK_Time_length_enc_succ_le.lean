-- Prove2me | Theorems.Thm_UniformInK_Time_length_enc_succ_le
-- name    : UniformInK.Time.length_enc_succ_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:03:40.061743+00:00
-- url     : https://prove2.me/theorems/57fa7c25-7dc0-40e9-9922-7f5e6100535d
-- title:
--   Time: length enc succ le
-- statement:
--   The length of the code of (k, φ), plus one, is at most (n+2)^(5k), for a k-CNF φ on n variables
--   and k ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Top/Time.lean#L28-L48
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Top/Time.lean#L28-L48

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInK_Top_Defs
import Definitions.Def_ClauseBound_TopN_End
import Definitions.Def_ClauseBound_Alg_End
import Definitions.Def_WidthK_Decode
import Definitions.Def_UniformInK_Top_Time
import Theorems.Thm_ClauseBound_Alg_End_length_enc_succ_le
import Theorems.Thm_Groundwork_DecodeK_length_enc_succ_le
import Theorems.Thm_Groundwork_Decode_length_enc_succ_le
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open UniformInK
open Groundwork PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.Alg.End ClauseBound.TopN ClauseBound.TopN.End
open UniformInK.Time

theorem UniformInK.Time.length_enc_succ_le {k n : ℕ} {φ : Sat3.CNF n} (hk : 1 ≤ k) (h : SatK.IsKCNF k φ) : (SatM.enc k φ).length + 1 ≤ (n + 2) ^ (5 * k) := by sorry
