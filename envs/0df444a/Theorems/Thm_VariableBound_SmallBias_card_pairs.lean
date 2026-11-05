-- Prove2me | Theorems.Thm_VariableBound_SmallBias_card_pairs
-- name    : VariableBound.SmallBias.card_pairs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:08:44.35404+00:00
-- url     : https://prove2.me/theorems/e8baff6f-129e-405a-811c-5d03f3934ecc
-- title:
--   Small Bias: card pairs
-- statement:
--   The number of pairs with a property is the sum, over the first entry, of the number of second
--   entries.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Family/SmallBias.lean#L95-L97
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Family/SmallBias.lean#L95-L97

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_AppVariablesStatement
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.ZMod.Basic
import Definitions.Def_VariableBound_Family_SmallBias
set_option autoImplicit false
section
section
open VariableBound VariableBound.SmallBias
open Finset AppVariables

theorem VariableBound.SmallBias.card_pairs {A : Type} [Fintype A] (Q : A × A → Prop) [DecidablePred Q] : #{p : A × A | Q p} = ∑ a : A, #{b : A | Q (a, b)} := by sorry
