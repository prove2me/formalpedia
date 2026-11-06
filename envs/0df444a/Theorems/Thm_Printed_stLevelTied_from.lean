-- Prove2me | Theorems.Thm_Printed_stLevelTied_from
-- name    : Printed.stLevelTied_from
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:19:26.29273+00:00
-- url     : https://prove2.me/theorems/5bda70ba-b91c-4f1c-be14-329b56ee4daf
-- title:
--   Printed: st Level Tied from
-- statement:
--   Proposition 3, first sentence, for the algorithm of its proof, from Lemma 1 for the algorithm of
--   its proof.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/LevelFrom.lean#L36-L36
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/LevelFrom.lean#L36-L36

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_LevelSentences
import Definitions.Def_Printed_LevelPoly
import Definitions.Def_Printed_GroupingPoly
import Definitions.Def_Printed_LevelFrom
set_option autoImplicit false
section
section
open Printed

theorem Printed.stLevelTied_from (hG : StGroupingTied) : StLevelTied := by sorry
