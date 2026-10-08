-- Prove2me | Theorems.Thm_TrulySubcubicAPSP_exactTriangle
-- name    : TrulySubcubicAPSP.exactTriangle
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-06T05:12:20.336072+00:00
-- url     : https://prove2.me/theorems/86662280-ad77-4341-89f6-2a606cd717da
-- title:
--   Theorem 19 — Exact Triangle in $O(n^{2.9983})$ steps
-- statement:
--   For every fixed $\kappa\in\mathbb N$, there exist one finite deterministic word-RAM program $P$, one natural constant $b$, and one step-bound function $T$ that work for every input size $n$, including $n=0,1$, and for every word width $W\ge b(\operatorname{Nat.log2}(n)+1)$. All encoded input numbers have absolute value at most $n^\kappa$. The run must halt with the specified verdict and output within $T(n)$ steps.
--
--   Given three $n\times n$ integer matrices $w_{AB},w_{BC},w_{AC}$, decide whether there exist indices $a,b,c$ with $w_{AB}(a,b)+w_{BC}(b,c)+w_{AC}(a,c)=0$. The algorithm accepts if and only if such indices exist, and
--   $$T(n)=O(n^{3-0.0017})=O(n^{2.9983}).$$
--
--   This is the corresponding known result extracted from the source formalization, presented here as an open proof obligation.
-- source:
--   https://arxiv.org/abs/2610.06783; Theorem 19; EndStatement.lean lines 75–86; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/EndStatement.lean

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_TrulySubcubicAPSP_Problems

set_option autoImplicit false
set_option relaxedAutoImplicit false

theorem TrulySubcubicAPSP.exactTriangle :
    TrulySubcubicAPSP.ExactTriangle.SolvedInTime (3 - TrulySubcubicAPSP.ε_T) := by sorry
