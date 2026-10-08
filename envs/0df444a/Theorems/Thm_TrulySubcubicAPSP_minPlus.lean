-- Prove2me | Theorems.Thm_TrulySubcubicAPSP_minPlus
-- name    : TrulySubcubicAPSP.minPlus
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-06T05:26:53.43098+00:00
-- url     : https://prove2.me/theorems/9e8880fc-4529-43b9-acc2-b645199a513c
-- title:
--   Theorem 22 — Min-plus product in $O(n^{2.99942})$ steps
-- statement:
--   For every fixed $\kappa\in\mathbb N$, there exist one finite deterministic word-RAM program $P$, one natural constant $b$, and one step-bound function $T$ that work for every input size $n$, including $n=0,1$, and for every word width $W\ge b(\operatorname{Nat.log2}(n)+1)$. All encoded input numbers have absolute value at most $n^\kappa$. The run must halt with the specified verdict and output within $T(n)$ steps.
--
--   Given integer matrices $A,B\in\mathbb Z^{n\times n}$, accept and output their exact $(\min,+)$-product, row by row:
--   $$C_{ij}=\min_{k<n}(A_{ik}+B_{kj}),\qquad T(n)=O(n^{2.99942}).$$
--   For $n=0$ there are no output entries. Each required entry for nonempty matrices is both attained by a candidate sum and no larger than any candidate sum.
--
--   This is the corresponding known result extracted from the source formalization, presented here as an open proof obligation.
-- source:
--   https://arxiv.org/abs/2610.06783; Theorem 22, second bound using Corollary 26; EndStatement.lean lines 98–107; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/EndStatement.lean

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_TrulySubcubicAPSP_Problems

set_option autoImplicit false
set_option relaxedAutoImplicit false

theorem TrulySubcubicAPSP.minPlus :
    TrulySubcubicAPSP.MinPlusProduct.SolvedInTime 2.99942 := by sorry
