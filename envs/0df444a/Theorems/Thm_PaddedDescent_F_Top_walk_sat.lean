-- Prove2me | Theorems.Thm_PaddedDescent_F_Top_walk_sat
-- name    : PaddedDescent.F.Top.walk_sat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:23:06.357285+00:00
-- url     : https://prove2.me/theorems/de69982a-61ed-451b-8de6-ce1d629e1872
-- title:
--   Top: walk sat
-- statement:
--   The walk whose test is «the count is positive» decides satisfiability: width k ≥ 1, n variables
--   with sOf n ≥ s0K k, at most inLen k n clauses of 1 to k literals, and a pad of
--   length at least 2^(8·(n / 2^(sOf n) + 1)).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/Top.lean#L162-L180
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/Top.lean#L162-L180

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_NSat
import Definitions.Def_ToTuring_EncLemmas
import Definitions.Def_SparsifyWidthK_Step
import Definitions.Def_SparsifyWidthK_SetAlg
import Definitions.Def_SparsifyWidthK_Thresholds
import Definitions.Def_SparsifyWidthK_Refine
import Definitions.Def_SparsifyWidthK_ProgMain
import Definitions.Def_PaddedDescent_F_Top
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Top
open Finset Groundwork Groundwork.Prog
open Groundwork.Sparsify (PFml leaves rootP roundB round)
open WidthK (theta bsum leafC)
open WidthK.Prog (stepK)
open PaddedDescent.F.Mark (WfL occ nSat)

theorem PaddedDescent.F.Top.walk_sat (hCount : StCountM) (hLf : StLeaf) (hSched : StSched) (hA : StA) (hAW : StAW) {k n : ℕ} (hk : 1 ≤ k) (hs : s0K k ≤ sOf n)
    (pad : U) (hF : 2 ^ (8 * (n / 2 ^ sOf n + 1)) ≤ pad.length) (ψ : Fml) (hψl : ψ.length ≤ inLen k n)
    (hψne : ∀ C ∈ ψ, C ≠ [] ∧ C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) :
    walkF k pad (tauOf (sOf n))
      (fun x => decide (0 < countM k pad ((schedF pad (depthOf (sOf n))).1, (schedF pad (depthOf (sOf n))).2.1) (markPar n (sOf n)) (layersOf (sOf n)) x))
      (rootP ψ) = true ↔ Fml.Sat ψ := by sorry
