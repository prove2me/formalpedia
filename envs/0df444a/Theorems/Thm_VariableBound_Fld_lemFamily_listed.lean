-- Prove2me | Theorems.Thm_VariableBound_Fld_lemFamily_listed
-- name    : VariableBound.Fld.lemFamily_listed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:06:07.692138+00:00
-- url     : https://prove2.me/theorems/469c0b11-2c2f-4d8a-bee5-618d8afc84d4
-- title:
--   Fld: lem Family listed
-- statement:
--   Lemma 13 (Family of checks) with its second sentence: the list `famD m a` is computed in
--   polynomial time, jointly in m and a, both given in unary; and for v = 2^a with 2 ≤ v ≤ m it is not
--   empty, has fewer than (32m)⁴
--   members, every member is an increasing list of numbers below m, and the members, indexed by their
--   places in the list, have (a), (b), (c). That the list is not empty is in the printed proof (|Ω| ≥
--   (15/16)·|𝔽|⁴), not in the
--   printed statement.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Main.lean#L37-L37
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Main.lean#L37-L37

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Field_Family
import Definitions.Def_VariableBound_Field_Cert
import Definitions.Def_VariableBound_Family_Main
import Definitions.Def_VariableBound_Field_Main
set_option autoImplicit false
section
section
open VariableBound VariableBound.Fld

theorem VariableBound.Fld.lemFamily_listed : StCertFamD ∧ StFamD := by sorry
