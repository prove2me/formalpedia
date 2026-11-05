-- Prove2me | Theorems.Thm_PaddedDescent_F_CertTop_polyT_roundB
-- name    : PaddedDescent.F.CertTop.polyT_roundB
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:16:57.146926+00:00
-- url     : https://prove2.me/theorems/9d9dac78-64e0-466d-92b6-7fc9c8468866
-- title:
--   Cert Top: poly T round B
-- statement:
--   One round of the depth-first walk is polynomial-time, for a step function and a test that may
--   depend on the context.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertSparsify.lean#L84-L87
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertSparsify.lean#L84-L87

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_SparsifyWidthK_Poly_Sparsify
import Definitions.Def_PaddedDescent_F_CertSparsify
import Theorems.Thm_WidthK_Prog_pickK_eq

set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.CertTop
open Groundwork Groundwork.Sparsify
open WidthK (thrPair theta)
open WidthK.Prog (pairsK pickK pickK_eq stepK)
variable {α σ : Type} [Enc α] [Enc σ]

theorem PaddedDescent.F.CertTop.polyT_roundB {step : α → σ → Option (σ × σ)} {test : α → σ → Bool} {st : α → List σ × Bool}
    (h1 : PolyT fun p : α × σ => step p.1 p.2) (h2 : PolyT fun p : α × σ => test p.1 p.2) (h3 : PolyT st) :
    PolyT fun x => roundB (step x) (test x) (st x) := by sorry
