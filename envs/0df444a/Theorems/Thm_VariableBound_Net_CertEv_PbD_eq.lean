-- Prove2me | Theorems.Thm_VariableBound_Net_CertEv_PbD_eq
-- name    : VariableBound.Net.CertEv.PbD_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:42:30.566589+00:00
-- url     : https://prove2.me/theorems/19eeef30-00c5-4442-a9a1-7c48596f4b52
-- title:
--   Cert Ev: Pb D eq
-- statement:
--   The bound P that does not depend on the formula, in natural numbers, with g = 3K⁸.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/CertEv.lean#L50-L52
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/CertEv.lean#L50-L52

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

theorem VariableBound.Net.CertEv.PbD_eq (K n Δ : ℕ) :
    PbD K n Δ = 2 * (qv (3 * K ^ 8) n * (1 + Δ * (tbMax n Δ + 3)) + qv (3 * K ^ 8) (10 * n) * sbMax Δ) := by sorry
