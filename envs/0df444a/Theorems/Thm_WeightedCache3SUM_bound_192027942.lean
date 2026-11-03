-- Prove2me | Theorems.Thm_WeightedCache3SUM_bound_192027942
-- name    : WeightedCache3SUM.bound_192027942
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-02T15:59:31.656136+00:00
-- url     : https://prove2.me/theorems/807964b0-aab0-4733-b4ac-19a05091056f
-- title:
--   3SUM in $O(n^{1.92027942})$ word-RAM steps
-- statement:
--   For every fixed $\kappa\in\mathbb N$, there exist a finite deterministic word-RAM program $P$, a natural constant $b$, and a step-bound function $T$ that work for every input size $n$ and every word width $W\ge b(\operatorname{Nat.log2}(n)+1)$. On integers $x_0,\ldots,x_{n-1}$ with $|x_i|\le n^\kappa$, the program halts within $T(n)$ steps and accepts exactly when there are pairwise distinct indices $i,j,k$ with $x_i+x_j+x_k=0$.
--
--   The exponent is exactly $r=96013971/50000000=1.92027942$. The foundation definition `EndStatement.BigO T r` requires a natural constant $K$ such that $T(n)^{r.\mathrm{den}}\le K n^{r.\mathrm{num}.\mathrm{toNat}}$ for every $n\ge2$. Thus $T(n)=O(n^{1.92027942})$. Repeated values at distinct positions are allowed; no witness triple is required, and inputs with $n<3$ must be rejected.
--
--   This is the statement of Jionghan Wang's `Race.bound` at source commit ac885d10bdbf723c3e0549198f9345bedf2a4131, using the campaign's existing foundation definitions.
-- source:
--   https://arxiv.org/abs/2610.06783v1; Theorem 22, second bound using Corollary 26; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/EndStatement.lean#L88-L97; EndStatement.Theorem_22_3SUM.

import Definitions.Def_TrulySubcubicAPSP_SourceSpecification

set_option autoImplicit false
set_option relaxedAutoImplicit false

theorem WeightedCache3SUM.bound_192027942 :
    EndStatement.ThreeSum.SolvedInTime (96013971 / 50000000 : Rat) := by sorry
