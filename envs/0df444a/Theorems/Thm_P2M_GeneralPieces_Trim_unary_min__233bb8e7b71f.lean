-- Prove2me | Theorems.Thm_P2M_GeneralPieces_Trim_unary_min__233bb8e7b71f
-- name    : P2M_GeneralPieces_Trim_unary_min__233bb8e7b71f
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:34:49.982219+00:00
-- url     : https://prove2.me/theorems/d6398773-e8b8-46b7-84ce-f4981363907a
-- title:
--   P2 M General Pieces Trim unary min  233bb8e7b71f: P2 M General Pieces Trim unary min  233bb8e7b71f
-- statement:
--   The smaller of two numbers, the second of which is given in unary, is given in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Trim/Cert.lean#L31-L32
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Trim/Cert.lean#L31-L32

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Trim_Prog
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_GeneralPieces_Trim_Cert
set_option autoImplicit false
section
section
open GeneralPieces
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.Gen
open GeneralPieces.Trim
variable {α : Type} [Enc α] {P : PiecesF}

theorem P2M_GeneralPieces_Trim_unary_min__233bb8e7b71f {f g : α → ℕ} (hf : PolyT f) (hg : Unary g) : Unary fun x => min (f x) (g x) := by sorry

alias «GeneralPieces».«Trim».«unary_min'» := P2M_GeneralPieces_Trim_unary_min__233bb8e7b71f
