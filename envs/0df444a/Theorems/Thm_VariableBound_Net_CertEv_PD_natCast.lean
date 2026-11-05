-- Prove2me | Theorems.Thm_VariableBound_Net_CertEv_PD_natCast
-- name    : VariableBound.Net.CertEv.PD_natCast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:40:54.005307+00:00
-- url     : https://prove2.me/theorems/84fa34ff-479a-43f2-881d-e47f021261f2
-- title:
--   Cert Ev: PD nat Cast
-- statement:
--   P = ⌈2P₀⌉ for a natural number s̄: 2·(⌈n/g⌉(1 + Δ(t̄ + 3)) + ⌈r̄/g⌉·s̄).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/CertEv.lean#L43-L47
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/CertEv.lean#L43-L47

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

theorem VariableBound.Net.CertEv.PD_natCast (g n Δ tb rb sb : ℕ) : PD g n Δ tb rb (sb : ℚ) = 2 * (qv g n * (1 + Δ * (tb + 3)) + qv g rb * sb) := by sorry
