-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P91_rule_4
-- name    : QAlgorithms.Papers.Independent.Intake100.P91.rule_4
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:12:20.257664+00:00
-- url     : https://prove2.me/theorems/f8651638-65b8-4a50-91c5-64c13b84893d
-- title:
--   Pattern Rule 4: remove common full columns, then use Rule 2
-- statement:
--   Let $n,k,a,b$ be nonnegative integers with $k\ge1$, $n\ge2k$, $k-1\le a\le n-k$, $k\le b\le n-k$, and $b=a$ or $b=a+1$. Let $\alpha(r,s,a;R,S,b)$ denote the real Louck product (17)–(18) for the lower and upper qubit GT patterns specified by its arguments. Removing their $k-1$ common full columns gives
--
--   $$
--   \alpha(n-k,k-1,a;n-k,k,b)=
--   \alpha(n-2k+1,0,a-k+1;n-2k+1,1,b-k+1).
--   $$
--
--   The coefficient is therefore
--
--   $$
--   \alpha(n-k,k-1,a;n-k,k,b)=
--   \begin{cases}
--   \sqrt{(b-k+1)/(n-2k+2)},&a=b,\\
--   -\sqrt{(n-k-b+1)/(n-2k+2)},&b=a+1.
--   \end{cases}
--   $$
--
--   The denominator is at least $2$. The rule includes $k=1$, when no columns are removed.
--
--   **Formalization Note** The minus lost after the first expression in (45) is retained; the reference to Rule 1b following (46) is read as Rule 2b, consistently with Rule 4 and the examples.
-- source:
--   A Multigraph Approach for Performing the Quantum Schur Transform, arXiv:2204.10694v1, PDF p. 13, §4.1, Rule 4; Appendix A, (42)–(46)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P91

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P91

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- Rule 4, PDF p.13, proved p.20, (42)-(46): delete k-1 complete columns,
then apply Rule 2. Includes k=1. Correction: (45) loses its minus after the
first equality; the prose after (46) prints Rule 1b where Rule 2b is needed.
The retained minus agrees with Rule 4 and all three examples, pp.13-14. -/
theorem rule_4 (n k a b : ℕ) (hk : 1 ≤ k) (hn : 2*k ≤ n)
    (haLower : k-1 ≤ a) (haUpper : a ≤ n-k)
    (hbLower : k ≤ b) (hbUpper : b ≤ n-k) (hedge : b = a ∨ b = a+1) :
    qubitLouck (n-k) (k-1) a (n-k) k b =
      qubitLouck (n-2*k+1) 0 (a-(k-1)) (n-2*k+1) 1 (b-(k-1)) ∧
    qubitLouck (n-k) (k-1) a (n-k) k b =
      if a = b then Real.sqrt (((b : ℝ) - k + 1) / ((n : ℝ) - 2*k + 2))
      else -Real.sqrt (((n : ℝ) - k - b + 1) / ((n : ℝ) - 2*k + 2)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P91

end
