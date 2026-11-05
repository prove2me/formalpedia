-- Prove2me | Theorems.Thm_VariableBound_Net_CertEv_UbD_unary
-- name    : VariableBound.Net.CertEv.UbD_unary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:51:33.608971+00:00
-- url     : https://prove2.me/theorems/b5b916fd-1c05-4b06-aaec-52db0aed4cf1
-- title:
--   Cert Ev: Ub D unary
-- statement:
--   The bound on the total U in «The total» of Step 3, with the logarithms rounded up, is given in
--   unary if k, K, n and Δ are.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/CertEv.lean#L70-L73
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/CertEv.lean#L70-L73

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

theorem VariableBound.Net.CertEv.UbD_unary {k K n Δ : α → ℕ} (hk : Unary k) (hK : Unary K) (hn : Unary n) (hΔ : Unary Δ) : Unary fun x => UbD (k x) (K x) (n x) (Δ x) := by sorry
