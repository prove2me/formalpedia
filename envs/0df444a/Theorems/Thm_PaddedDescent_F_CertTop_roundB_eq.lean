-- Prove2me | Theorems.Thm_PaddedDescent_F_CertTop_roundB_eq
-- name    : PaddedDescent.F.CertTop.roundB_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:17:02.934015+00:00
-- url     : https://prove2.me/theorems/40e6c938-b52c-461d-93be-95c723580c2c
-- title:
--   Cert Top: round B eq
-- statement:
--   `roundB` with its case distinctions written by eliminators.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertSparsify.lean#L74-L80
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertSparsify.lean#L74-L80

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_SparsifyWidthK_Poly_Sparsify
import Definitions.Def_PaddedDescent_F_CertSparsify
import Theorems.Thm_Groundwork_PolyT_elim
import Theorems.Thm_WidthK_Prog_pickK_eq

set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.CertTop
open Groundwork Groundwork.Sparsify
open WidthK (thrPair theta)
open WidthK.Prog (pairsK pickK pickK_eq stepK)
variable {α σ : Type} [Enc α] [Enc σ]
omit [Enc σ]

theorem PaddedDescent.F.CertTop.roundB_eq (step : σ → Option (σ × σ)) (test : σ → Bool) (st : List σ × Bool) :
    roundB step test st = st.1.head?.elim ([], st.2) fun s =>
      (step s).elim (st.1.tail, test s || st.2) fun lh => (lh.1 :: lh.2 :: st.1.tail, st.2) := by sorry
