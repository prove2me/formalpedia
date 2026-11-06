-- Prove2me | Theorems.Thm_ThmCount_wrapper_counts
-- name    : ThmCount.wrapper_counts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:41:40.127787+00:00
-- url     : https://prove2.me/theorems/65999d87-b623-4ce8-ae1e-7aa9fbb398c0
-- title:
--   Thm Count: wrapper counts
-- statement:
--   Every machine N that wraps a machine M with the body of Theorem D(b), with a front end that adds
--   four forced variables and with `dropFour` as the last step, computes the number of satisfying
--   assignments of every 3-CNF on n variables within q·(time of M on n + 4 variables + a·(n+2)^d + 1)^q
--   steps, if a·(n+2)^d bounds the length of the plain code.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/ThmCount/Main.lean#L38-L51
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/ThmCount/Main.lean#L38-L51

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThmCount_Defs
import Definitions.Def_ThmCount_FrontEnd
import Definitions.Def_ThmCount_Rates
import Definitions.Def_Wrap_Main
import Mathlib.Tactic
import Definitions.Def_ThmCount_Main
import Theorems.Thm_ClauseBound_Inst_Half_CertSmall_d
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open ThmCount
open Turing Groundwork PaperSentences

theorem ThmCount.wrapper_counts {a d : ℕ} (hl : ∀ (n : ℕ) (φ : Sat3.CNF n), SatK.IsKCNF 3 φ → (SatK.enc 3 φ).length ≤ a * (n + 2) ^ d)
    {M : TM2ComputableAux Bool Bool} {C : ℕ} (hM : MainTheoremForms.ThmVariablesBFor M C) {pre : List Bool → List Bool} (hpre : MapsToPadded pre)
    {N : TM2ComputableAux Bool Bool} {q : ℕ} (hW : Wrap.Wraps M pre dropFour N q) :
    SatK.CountsTM 3 N fun n => q * (MainTheoremForms.timeN C 3 (n + 4) + a * (n + 2) ^ d + 1) ^ q := by sorry
