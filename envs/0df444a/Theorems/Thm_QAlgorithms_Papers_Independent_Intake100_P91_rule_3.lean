-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P91_rule_3
-- name    : QAlgorithms.Papers.Independent.Intake100.P91.rule_3
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:11:37.104315+00:00
-- url     : https://prove2.me/theorems/16f95829-768c-4966-b21b-f5f246092041
-- title:
--   Pattern Rule 3: remove all common full columns, then use Rule 1
-- statement:
--   Let $n,k,a,b$ be nonnegative integers with $n\ge2k+1$, $k\le a\le n-k-1$, $k\le b\le n-k$, and $b=a$ or $b=a+1$. Let $\alpha(r,s,a;R,S,b)$ be the real Louck product (17)–(18) between the lower and upper qubit GT patterns specified by these arguments. Removing the $k$ common full columns preserves the coefficient:
--
--   $$
--   \alpha(n-k-1,k,a;n-k,k,b)=
--   \alpha(n-2k-1,0,a-k;n-2k,0,b-k).
--   $$
--
--   Its value is
--
--   $$
--   \alpha(n-k-1,k,a;n-k,k,b)=
--   \begin{cases}
--   \sqrt{(n-k-b)/(n-2k)},&a=b,\\
--   \sqrt{(b-k)/(n-2k)},&b=a+1.
--   \end{cases}
--   $$
--
--   Both branches are positive, and $n-2k\ge1$. This reduces two-row coefficients to the one-row rule and includes $k=0$.
-- source:
--   A Multigraph Approach for Performing the Quantum Schur Transform, arXiv:2204.10694v1, PDF p. 13, §4.1, Rule 3; Appendix A, (37)–(41)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P91

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P91

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- Rule 3, PDF p.13, proved p.19, (37)-(41): delete k complete columns.
The conjunction retains both the reduction to Rule 1 and its numerical value.
Includes k=0 (Rule 1). A valid lower shape requires n≥2k+1. -/
theorem rule_3 (n k a b : ℕ) (hn : 2*k+1 ≤ n)
    (haLower : k ≤ a) (haUpper : a ≤ n-k-1)
    (hbLower : k ≤ b) (hbUpper : b ≤ n-k) (hedge : b = a ∨ b = a+1) :
    qubitLouck (n-k-1) k a (n-k) k b =
      qubitLouck (n-2*k-1) 0 (a-k) (n-2*k) 0 (b-k) ∧
    qubitLouck (n-k-1) k a (n-k) k b =
      if a = b then Real.sqrt (((n : ℝ) - k - b) / ((n : ℝ) - 2*k))
      else Real.sqrt (((b : ℝ) - k) / ((n : ℝ) - 2*k)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P91

end
