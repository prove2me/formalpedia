-- Prove2me | Theorems.Thm_PrivateContinualCounting_Kraft_hilbert_inequality
-- name    : PrivateContinualCounting.Kraft.hilbert_inequality
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T06:43:22.936799+00:00
-- url     : https://prove2.me/theorems/e6bc5529-3a53-4541-843f-c0838b286195
-- title:
--   Hilbert's inequality for $\chi_j=\sum_k \beta_k/(j+k+1)$
-- statement:
--   This is the form of Hilbert's inequality used in the proof of Theorem 3.1.
--
--   Let $(\beta_k)_{k\ge0}$ be nonnegative real numbers with $\sum_{k\ge0}\beta_k^2<\infty$, and for $j\ge0$ put
--
--   $$\chi_j=\sum_{k\ge0}\frac{\beta_k}{j+k+1}.$$
--
--   Then:
--
--   1. every series defining $\chi_j$ converges;
--   2. $\sum_{j\ge0}\chi_j^2<\infty$;
--   3. the budget bound
--   $$\sum_{j\ge0}\chi_j^2\le 16\sum_{k\ge0}\beta_k^2$$
--   holds.
--
--   In the source, Hilbert's inequality $\sum_{j,k\ge0}a_jb_k/(j+k+1)\le\pi\|a\|\|b\|$ gives $\|\chi\|\le\pi\|r\|$ with $\beta_k=\|r_k\|$. The statement here records the same estimate with the constant $4$ in place of $\pi$ (so $16$ in place of $\pi^2$); every use in Theorem 1.1 needs only that the budget $\|\chi\|^2$ is a finite multiple of $\|r\|^2$.
--
--   The inequality bounds the total strategy budget that one time-invariant counter can distribute over all time scales. It is the analytic input of Theorem 3.1 and of the Kraft-necessity argument of §3.2.
--
--   **Formalization Note** The three conclusions are stated separately, so no divergent real `tsum` is ever read as zero.
-- source:
--   Kisung Park, Sharp Limits of Time Invariance in Private Continual Counting, STOC 2027 submission #86 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/86.pdf, p. 7 (PDF p. 9), proof of Theorem 3.1: Hilbert's inequality [HLP52, Ch. IX] gives ‖χ‖ ≤ π‖r‖ by duality (recorded here with the Schur-test constant 4 in place of π).

import Mathlib

set_option autoImplicit false

namespace PrivateContinualCounting.Kraft

/-- Hilbert's inequality in the form used for Theorem 3.1 (Schur-test constant 4 in place of π). -/
theorem hilbert_inequality (β : ℕ → ℝ) (hβ : ∀ k, 0 ≤ β k)
    (hβ2 : Summable (fun k => β k ^ 2)) :
    (∀ j : ℕ, Summable (fun k : ℕ => β k / ((j : ℝ) + k + 1))) ∧
    Summable (fun j : ℕ => (∑' k : ℕ, β k / ((j : ℝ) + k + 1)) ^ 2) ∧
    ∑' j : ℕ, (∑' k : ℕ, β k / ((j : ℝ) + k + 1)) ^ 2 ≤ 16 * ∑' k : ℕ, β k ^ 2 := by sorry

end PrivateContinualCounting.Kraft
