-- Prove2me | Theorems.Thm_ThreeSum1962_threeSum_bound
-- name    : ThreeSum1962.threeSum_bound
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-13T19:37:33.280915+00:00
-- url     : https://prove2.me/theorems/faf3da56-8bce-41db-b7fb-332e1861ada2
-- title:
--   Deterministic 3SUM in $O(n^{1.962})$ word-RAM steps
-- statement:
--   For every fixed $\kappa\in\mathbb N$, there exist a finite deterministic word-RAM program $P$, a natural constant $b$, and a step-bound function $T$ that work for every input size $n$ and every word width $W\ge b(\operatorname{Nat.log2}(n)+1)$. On integers $x_0,\ldots,x_{n-1}$ with $|x_i|\le n^\kappa$, the program halts within $T(n)$ steps and accepts exactly when there are pairwise distinct indices $i,j,k$ with $x_i+x_j+x_k=0$.
--
--   For the rational exponent $r=1.962$, the bound is the foundation definition `EndStatement.BigO T r`: there is a natural constant $K$ such that $T(n)^{r.\mathrm{den}}\le K n^{r.\mathrm{num}.\mathrm{toNat}}$ for every $n\ge2$. For nonnegative $r$, this is $T(n)=O(n^r)$. Repeated values at distinct positions are allowed; no witness triple is required, and inputs with $n<3$ must be rejected.
--
--   Use the foundation mission’s existing definitions without restating them.
--
--   The exponent is exactly $981/500$. The source theorem is `Race.bound`, proved by `ThreeSum.solvedInTime_981_500`; the source repository reports completed local proof and axiom checks. The complete proof remains in the cited repository; this proposal includes source links only and does not establish Prove2Me proof acceptance.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission.lean#L1-L8; proof: https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/FinalSolver.lean#L17-L24; source commit 2b639655e07421b9ac743de9090459bab473a7c0

import Definitions.Def_TrulySubcubicAPSP_SourceSpecification

set_option autoImplicit false
set_option relaxedAutoImplicit false

theorem ThreeSum1962.threeSum_bound :
    EndStatement.ThreeSum.SolvedInTime 1.962 := by sorry
