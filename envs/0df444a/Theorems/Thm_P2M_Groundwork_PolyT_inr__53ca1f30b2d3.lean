-- Prove2me | Theorems.Thm_P2M_Groundwork_PolyT_inr__53ca1f30b2d3
-- name    : P2M_Groundwork_PolyT_inr__53ca1f30b2d3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:46:27.451194+00:00
-- url     : https://prove2.me/theorems/79dfa321-a281-408a-a4de-214aa60ce03d
-- title:
--   P2 M Groundwork Poly T inr  53ca1f30b2d3: P2 M Groundwork Poly T inr  53ca1f30b2d3
-- statement:
--   The P2 M Groundwork Poly T inr  53ca1f30b2d3 construction uses the P2 M Groundwork Poly T inr  53ca1f30b2d3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Closure/Basic.lean#L125-L126
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Closure/Basic.lean#L125-L126

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_PolyT
import Definitions.Def_ToTuring_EncLemmas
import Definitions.Def_ToTuring_Closure_Basic
set_option autoImplicit false
section
section
open Groundwork Groundwork.PolyT
open TM Enc
variable {α β γ δ ε : Type} [Enc α] [Enc β] [Enc γ] [Enc δ] [Enc ε]

theorem P2M_Groundwork_PolyT_inr__53ca1f30b2d3 {f : α → γ} (hf : PolyT f) : PolyT (fun x => (Sum.inr (f x) : β ⊕ γ)) := by sorry

alias «Groundwork».«PolyT».«inr'» := P2M_Groundwork_PolyT_inr__53ca1f30b2d3
