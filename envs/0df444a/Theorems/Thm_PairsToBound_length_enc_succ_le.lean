-- Prove2me | Theorems.Thm_PairsToBound_length_enc_succ_le
-- name    : PairsToBound.length_enc_succ_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T00:59:19.572102+00:00
-- url     : https://prove2.me/theorems/37af5baa-bfc5-488f-8c2f-39dcddc5c8af
-- title:
--   Pairs To Bound: length enc succ le
-- statement:
--   «… as there are fewer than (2n+1)^k ≤ n^(2k) clauses …, reading the input included»: the code of
--   (k, φ), for k ≥ 1 and a k-CNF φ on n ≥ 2 variables, has fewer than n^(8k) symbols.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/PairsToBound/Exhaust.lean#L99-L132
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/PairsToBound/Exhaust.lean#L99-L132

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PairsToBound_Width
import Definitions.Def_VariableBound_Paper_Forms
import Definitions.Def_ClauseBound_Alg_Decode
import Definitions.Def_ClauseBound_Alg_End
import Definitions.Def_CountKSat_InOut
import Definitions.Def_CountKSat_Poly
import Definitions.Def_CountKSatRate_Brute
import Definitions.Def_CountKSatRate_Cert
import Definitions.Def_CountKSatRate_Pad
import Definitions.Def_Wrap_Sim
import Definitions.Def_ToTuring_Closure_Basic
import Definitions.Def_ToTuring_Lib_List1b
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_PairsToBound_Exhaust
import Theorems.Thm_ClauseBound_Alg_End_length_enc_succ_le
import Theorems.Thm_Groundwork_DecodeK_length_enc_succ_le
import Theorems.Thm_Groundwork_Decode_length_enc_succ_le
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open PairsToBound
open Turing Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg Wrap MainTheoremForms
open Sat3 (CNF)

theorem PairsToBound.length_enc_succ_le {k n : ℕ} {φ : CNF n} (hk : 1 ≤ k) (hn : 2 ≤ n) (hφ : SatK.IsKCNF k φ) : (SatM.enc k φ).length + 1 ≤ n ^ (8 * k) := by sorry
