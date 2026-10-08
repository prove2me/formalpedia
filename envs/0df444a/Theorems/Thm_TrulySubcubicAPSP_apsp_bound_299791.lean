-- Prove2me | Theorems.Thm_TrulySubcubicAPSP_apsp_bound_299791
-- name    : TrulySubcubicAPSP.apsp_bound_299791
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-06T14:45:28.891007+00:00
-- url     : https://prove2.me/theorems/6bdc9821-d8c3-42ef-b58c-7932ad0f6d18
-- title:
--   APSP in $O(n^{2.99791})$ word-RAM steps
-- statement:
--   For every fixed $\kappa\in\mathbb N$, there exist one finite deterministic word-RAM program $P$, one natural constant $b$, and one step-bound function $T$ that work for every input size $n$, including $n=0,1$, and for every word width $W\ge b(\operatorname{Nat.log2}(n)+1)$. All encoded input numbers have absolute value at most $n^\kappa$. The run must halt with the specified verdict and output within $T(n)$ steps.
--
--   For a directed $n$-vertex graph with integer weights and no negative-weight closed walk, accept and compute every exact shortest-path distance in
--   $$T(n)=O(n^{2.99791}).$$
--   Each ordered vertex pair receives a flag and a distance. Reachable pairs have flag one and an attained minimum path weight; unreachable pairs have flag zero and an unconstrained distance slot. Negative edge weights and missing edges are permitted. Empty paths give diagonal distance zero. No assumptions about other algorithms appear in the theorem.
--
--   Establish this bound using the shared APSP and word-RAM definitions of the foundation mission.
-- source:
--   https://arxiv.org/abs/2610.06783 (Alman–Vassilevska Williams 2026), with refined exponent accounting: all-edges Exact Triangle route (footnote 10), exact binomial tail, pruned encodings, true middle dimension in the deterministic hashing reduction; parameters c=21.915, θ=0.116107, ε=0.055197.

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_TrulySubcubicAPSP_Problems

set_option autoImplicit false
set_option relaxedAutoImplicit false

theorem TrulySubcubicAPSP.apsp_bound_299791 :
    TrulySubcubicAPSP.APSP.SolvedInTime 2.99791 := by sorry
