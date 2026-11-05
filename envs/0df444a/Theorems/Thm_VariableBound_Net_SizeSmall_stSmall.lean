-- Prove2me | Theorems.Thm_VariableBound_Net_SizeSmall_stSmall
-- name    : VariableBound.Net.SizeSmall.stSmall
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:48:44.073459+00:00
-- url     : https://prove2.me/theorems/940a9508-4cab-4039-9c79-53f306382431
-- title:
--   Size Small: st Small
-- statement:
--   Step 3, «The parameters», the case m ≤ n̄ as printed: for g > 0, the empty list of checks, ψ
--   well formed (`WfD`) with at most n̄ clauses, every variable in at most Δ of them, and an admissible
--   profile y, the
--   network of y satisfies conditions (i) and (ii) of the definition of a network with P = 2⌈n/g⌉(1 + Δ)
--   and B = 1, and U ≤ 2(k − 1)n̄. That the profile is admissible is not used.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/SizeSmall.lean#L64-L73
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/SizeSmall.lean#L64-L73

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_SizeP
import Definitions.Def_VariableBound_Net_SizeSmall
set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.SizeSmall
open Groundwork Groundwork.Prog Finset
open PaddedDescent.F.Mark (qv occ)
variable {k g n Δ : ℕ}

theorem VariableBound.Net.SizeSmall.stSmall : StSmall := by sorry
