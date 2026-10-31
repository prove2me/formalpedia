-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P91_rule_1
-- name    : QAlgorithms.Papers.Independent.Intake100.P91.rule_1
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:10:24.600404+00:00
-- url     : https://prove2.me/theorems/72917f02-1e4a-4a47-80a5-895182c6a908
-- title:
--   Pattern Rule 1: adding a first-row box to a one-row tableau
-- statement:
--   Let $n\ge1$, and let $a,b$ be nonnegative integers satisfying $a\le n-1$, $b\le n$, and $b=a$ or $b=a+1$. Consider the qubit GT patterns with lower top row $(n-1,0)$ and zero count $a$, and upper top row $(n,0)$ and zero count $b$. Let $\alpha(r,s,a;R,S,b)$ denote their real transition coefficient calculated from Louck's product (17)–(18), with the first three arguments specifying the lower pattern. Then
--
--   $$
--   \alpha(n-1,0,a;n,0,b)=
--   \begin{cases}
--   \sqrt{(n-b)/n},&a=b,\\
--   \sqrt{b/n},&b=a+1.
--   \end{cases}
--   $$
--
--   This computes the coefficient by counting ones or zeroes in the upper tableau. For $n=1$ it gives both vacuum-to-one-qubit amplitudes as $1$.
-- source:
--   A Multigraph Approach for Performing the Quantum Schur Transform, arXiv:2204.10694v1, PDF p. 12, §4.1, Rule 1, (19)–(22); Appendix A, (33)–(34)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P91

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P91

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- Rule 1, PDF p.12, (19)-(22), proved p.18, (33)-(34).
Includes n=1 and the empty lower tableau. Both branches are positive. -/
theorem rule_1 (n a b : ℕ) (hn : 1 ≤ n) (ha : a ≤ n-1)
    (hb : b ≤ n) (hedge : b = a ∨ b = a+1) :
    qubitLouck (n-1) 0 a n 0 b =
      if a = b then Real.sqrt (((n : ℝ) - b) / (n : ℝ))
      else Real.sqrt ((b : ℝ) / (n : ℝ)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P91

end
