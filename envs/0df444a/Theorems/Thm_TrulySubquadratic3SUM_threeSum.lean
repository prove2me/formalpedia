-- Prove2me | Theorems.Thm_TrulySubquadratic3SUM_threeSum
-- name    : TrulySubquadratic3SUM.threeSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-06T07:20:08.779734+00:00
-- url     : https://prove2.me/theorems/07f62b7b-6f72-4cec-a1fd-eed6348830bf
-- title:
--   Theorem 22 — 3SUM in $O(n^{1.9992})$ steps
-- statement:
--   For every fixed $\kappa\in\mathbb N$, there exist a finite deterministic word-RAM program $P$, a natural constant $b$, and a step-bound function $T$ that work for every input size $n$ and every word width $W\ge b(\operatorname{Nat.log2}(n)+1)$. Given $n$ integers $x_0,\ldots,x_{n-1}$ with $|x_i|\le n^\kappa$, the program halts within $T(n)$ steps and accepts if and only if there are pairwise distinct indices $i,j,k$ such that $x_i+x_j+x_k=0$.
--
--   The time bound is $T(n)=O(n^{1.9992})$: precisely, there is a natural constant $K$ such that $T(n)^{1250}\le K n^{2499}$ for every $n\ge2$. The program must also halt and reject when $n<3$. Repeated integer values at different positions are allowed; no witness triple needs to be output.
--
--   This is exactly `EndStatement.Theorem_22_3SUM` from the accompanying formalization. It is the integer 3SUM part of Theorem 22, using Corollary 26, presented here as an open proof obligation.
-- source:
--   https://arxiv.org/abs/2610.06783v1; Theorem 22, second bound using Corollary 26; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/EndStatement.lean#L88-L97; EndStatement.Theorem_22_3SUM.

import Definitions.Def_TrulySubcubicAPSP_SourceSpecification

set_option autoImplicit false
set_option relaxedAutoImplicit false

theorem TrulySubquadratic3SUM.threeSum :
    EndStatement.ThreeSum.SolvedInTime 1.9992 := by sorry
