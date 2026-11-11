-- Prove2me | Theorems.Thm_SubexpPermanent_Main_lemma_6_1
-- name    : SubexpPermanent.Main.lemma_6_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:03:22.877898+00:00
-- url     : https://prove2.me/theorems/0119c30a-0eb9-454f-bc7c-10caa6f0170b
-- title:
--   Lemma 6.1 — the budgeted optimum is within $2\sqrt2\,n e^{-a/2}$ of $\log\operatorname{per}(A)$
-- statement:
--   Let $A$ be a nonnegative real $n\times n$ matrix with $\operatorname{per}(A)>0$, and $\mathrm{OPT}_A(a)=\min_{y\in D_a}\Phi_A(y)$. For every $a\ge0$,
--   $$\log\operatorname{per}(A)\le\mathrm{OPT}_A(a)\le\log\operatorname{per}(A)+2\sqrt2\,n\,e^{-a/2}\qquad(20).$$
--   This is the paper's analytic contribution. Under a budget $\Lambda=e^a$ on the total weight at each vertex, the best upper bound of the form (3) is within a factor $\exp(O(n/\sqrt\Lambda))$ of the permanent.
--
--   Differences from the source: none.
-- source:
--   Kudria, Luo, Majid, Subexponential Approximation of the Permanent in Deterministic Polynomial Time, arXiv:2609.10516 (held PDF, sha256 e752b6f0…), p. 21, Lemma 6.1, eq. (20)

import Mathlib
import Definitions.Def_SubexpPermanent_Main_Objective

namespace SubexpPermanent.Main

/-- Lemma 6.1 (error of the optimized upper bound), p. 21, eq. (20). -/
theorem lemma_6_1 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (hper : 0 < A.permanent) (a : ℝ) (ha : 0 ≤ a) :
    Real.log A.permanent ≤ OPT A a ∧
    OPT A a ≤ Real.log A.permanent + 2 * Real.sqrt 2 * n * Real.exp (-a / 2) := by sorry

end SubexpPermanent.Main
