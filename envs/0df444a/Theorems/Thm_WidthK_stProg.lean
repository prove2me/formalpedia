-- Prove2me | Theorems.Thm_WidthK_stProg
-- name    : WidthK.stProg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:16:38.839793+00:00
-- url     : https://prove2.me/theorems/b0235478-6d30-421f-88d2-35c60cb2485f
-- title:
--   Width K: st Prog
-- statement:
--   The sparsification lemma for width k for the program `stepK (theta τ) k`, from the other
--   interface statements.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/ProgMain.lean#L243-L255
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/ProgMain.lean#L243-L255

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyWidthK_Interfaces
import Mathlib.Tactic.Linarith
import Definitions.Def_SparsifyWidthK_ProgMain
set_option autoImplicit false
section
section
open WidthK
open Finset Groundwork Groundwork.Sparsify WidthK.Prog

theorem WidthK.stProg (h1 : StNodeRoot) (h2 : StNodeStep) (h3 : StNodeBound) (h4 : StLeafCard) (h5 : StLightEq) (h6 : StHeavyEq) (h7 : StSatIff)
    (h8 : StThr) (h9 : StBetaSum) (h10 : StRefines) : StProg := by sorry
