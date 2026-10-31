-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P91_rule_2
-- name    : QAlgorithms.Papers.Independent.Intake100.P91.rule_2
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:11:04.999396+00:00
-- url     : https://prove2.me/theorems/751b8e22-e057-49d3-9488-5c4df101029e
-- title:
--   Pattern Rule 2: adding a second-row box to a one-row tableau
-- statement:
--   Let $n\ge2$, $0\le a\le n-1$, $1\le b\le n-1$, and $b=a$ or $b=a+1$, with all parameters integral. The lower qubit GT pattern has top row $(n-1,0)$ and zero count $a$; the upper pattern has top row $(n-1,1)$ and zero count $b$. Write $\alpha(r,s,a;R,S,b)$ for the real Louck product (17)–(18) between the indicated patterns. Then
--
--   $$
--   \alpha(n-1,0,a;n-1,1,b)=
--   \begin{cases}
--   \sqrt{b/n},&a=b,\\
--   -\sqrt{(n-b)/n},&b=a+1.
--   \end{cases}
--   $$
--
--   The negative second branch fixes the source's singlet convention. In particular the two lower words $01$ and $10$ have coefficients $1/\sqrt2$ and $-1/\sqrt2$ at $n=2,b=1$.
--
--   **Formalization Note** The numerator's shape labels in (23)–(24) and the last sign in (36) are printing errors; the statement follows (25)–(26) and the first two expressions of (36).
-- source:
--   A Multigraph Approach for Performing the Quantum Schur Transform, arXiv:2204.10694v1, PDF p. 12, §4.1, Rule 2, (25)–(26); Appendix A, (35)–(36)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P91

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P91

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- Rule 2, PDF p.12, (25)-(26), proved pp.18-19, (35)-(36).
Correction: (23)-(24) print the nonexistent shape (n,0) in the numerator
labels. Equation (36)'s last equality drops a minus. We retain (26)'s minus,
consistent with (36)'s first two expressions and the singlet examples. -/
theorem rule_2 (n a b : ℕ) (hn : 2 ≤ n) (ha : a ≤ n-1)
    (hbLower : 1 ≤ b) (hbUpper : b ≤ n-1) (hedge : b = a ∨ b = a+1) :
    qubitLouck (n-1) 0 a (n-1) 1 b =
      if a = b then Real.sqrt ((b : ℝ) / (n : ℝ))
      else -Real.sqrt (((n : ℝ) - b) / (n : ℝ)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P91

end
