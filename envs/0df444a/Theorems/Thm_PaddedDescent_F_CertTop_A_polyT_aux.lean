-- Prove2me | Theorems.Thm_PaddedDescent_F_CertTop_A_polyT_aux
-- name    : PaddedDescent.F.CertTop.A_polyT_aux
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:17:36.730731+00:00
-- url     : https://prove2.me/theorems/1c1eec95-f22b-4f27-ae34-d16c43c5b3cf
-- title:
--   Cert Top: A poly T aux
-- statement:
--   The function `A` at any width k of the clauses, with the pad, the threshold τ, the schedule S,
--   the parameters q of the evaluations, the number R of layers (in unary) and the formula φ as
--   arbitrary functions of a context.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertA.lean#L26-L35
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertA.lean#L26-L35

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_CertTop
import Definitions.Def_PaddedDescent_F_CertEval
import Definitions.Def_PaddedDescent_F_CertA
set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.CertTop
open Groundwork Groundwork.Prog Groundwork.Prog.Count Groundwork.Sparsify
variable {α : Type} [Enc α]

theorem PaddedDescent.F.CertTop.A_polyT_aux (k : ℕ) (hV : StCertValF) (hM : StCertMark) (hA : StCertAdm) {S : α → List Lvl × U} {τ R : α → ℕ} {q : α → U × U × U × U}
    {φ : α → Fml} {pad : α → U} (hS : PolyT S) (hp : PolyT pad) (hτ : PolyT τ) (hq : PolyT q) (hR : Unary R) (hφ : PolyT φ) :
    PolyT fun p => bif hasNil (φ p) then false
      else walkF k (pad p) (τ p) (fun ψ => decide (0 < countM k (pad p) (S p) (q p) (R p) ψ)) (rootP (φ p)) := by sorry
