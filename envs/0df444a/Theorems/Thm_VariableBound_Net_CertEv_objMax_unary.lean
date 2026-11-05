-- Prove2me | Theorems.Thm_VariableBound_Net_CertEv_objMax_unary
-- name    : VariableBound.Net.CertEv.objMax_unary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:55:27.028724+00:00
-- url     : https://prove2.me/theorems/0d173fdf-2885-40f4-9a28-20de03678813
-- title:
--   Cert Ev: obj Max unary
-- statement:
--   The bound for the number I + m of objects is given in unary if n and Δ are.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/CertEv.lean#L65-L66
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/CertEv.lean#L65-L66

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Defs
import Definitions.Def_ClauseBound_ParityChecks_CertPar
import Definitions.Def_PaddedDescent_F_CertEval
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Ring
import Definitions.Def_VariableBound_Net_CertEv
import Theorems.Thm_PaddedDescent_F_Mark_Cert_qv_unary
attribute [local fun_prop] PaddedDescent.F.Mark.Cert.qv_unary


set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.CertEv
open Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.CertEval ClauseBound.Alg ClauseBound.ParityChecks ClauseBound.ParityChecks.CertLib ClauseBound.ParityChecks.CertPar
open PaddedDescent.F.Mark (qv nProf)
open PaddedDescent.F.Mark.Cert (qv_unary)
variable {α : Type} [Enc α]

theorem VariableBound.Net.CertEv.objMax_unary {n Δ : α → ℕ} (hn : Unary n) (hΔ : Unary Δ) : Unary fun x => objMax (n x) (Δ x) := by sorry
