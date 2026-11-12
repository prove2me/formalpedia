-- Prove2me | Theorems.Thm_SumsHighPowers_PITLifting_theorem_2_7_of_linearIndependent
-- name    : SumsHighPowers.PITLifting.theorem_2_7_of_linearIndependent
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T21:13:57.526321+00:00
-- url     : https://prove2.me/theorems/b268fe95-b311-4bc6-a63c-0515fe6e6504
-- title:
--   Theorem 2.7, linearly independent case — deg h₁ < (r − 2) Σ ν(hᵢ) when h₂, …, h_r are independent
-- statement:
--   Let $D, r \in \mathbb N$ with $r \ge 2$, and let $F$ be a field of characteristic $0$ or of characteristic $p > (r-1)D$. Let $h_1, h_2, \dots, h_r \in F[x]$ satisfy $h_2 + \dots + h_r = h_1$ and $\gcd(h_2, \dots, h_r) = 1$, with $\deg h_i \le D$ for all $i$, not all $h_i$ constant, no nonempty subsum of $h_2, \dots, h_r$ vanishing, and **$h_2, \dots, h_r$ linearly independent over $F$**. Then
--   $$\deg h_1 < (r-2)\sum_{i=1}^{r} \nu(h_i),$$
--   where $\nu(h)$ is the number of distinct roots of $h$ in the algebraic closure of $F$ (`numDistinctRoots`).
--
--   This is the case of `SumsHighPowers.PITLifting.theorem_2_7` (Theorem 2.7 of the mission *PIT and Reconstruction for Sums of High Powers*, p. 18, cited there from Vaserstein–Wheland, Theorem 2.2(a)) in which $h_2, \dots, h_r$ are linearly independent. Together with `SumsHighPowers.PITLifting.theorem_2_7_of_not_linearIndependent`, the dependent case, it gives Theorem 2.7. In the Lean statement, $h_2, \dots, h_r$ are `h 0, …, h (r − 2)`, the gcd condition says that every common divisor of them is a unit, and every binder is the one in `theorem_2_7`, plus the hypothesis `hli : LinearIndependent F h`. The no-vanishing-subsum hypothesis is kept so the binders match `theorem_2_7`; this case does not need it.
--
--   In this case the bound is Vaserstein–Wheland's Theorem 3.1 (L. N. Vaserstein and E. R. Wheland, *Vanishing polynomial sums*, Comm. Algebra 31(2) (2003) 751–772, https://doi.org/10.1081/AGB-120017341), and it holds in the stronger form $\deg h_1 + \binom{r-1}{2} \le (r-2)\sum_i \nu(h_i)$. The proof uses the Wronskian of $h_2, \dots, h_r$, which is nonzero because they are independent and have degree less than the characteristic.
-- source:
--   PIT and Reconstruction for Sums of High Powers (STOC 2027 submission 1653), §2.3, p. 18, Theorem 2.7 in the case where h_2, …, h_r are linearly independent, cited there from Vaserstein, L. N. and Wheland, E. R., Vanishing polynomial sums, Comm. Algebra 31(2) (2003) 751–772, https://doi.org/10.1081/AGB-120017341, Theorem 2.2(a) (the independent case is its Theorem 3.1)

import Mathlib
import Definitions.Def_SumsHighPowers_PITLifting_numDistinctRoots

namespace SumsHighPowers.PITLifting

theorem theorem_2_7_of_linearIndependent {F : Type*} [Field F] (D r : ℕ) (hr : 2 ≤ r)
    (hchar : ringChar F = 0 ∨ (r - 1) * D < ringChar F)
    (h₁ : Polynomial F) (h : Fin (r - 1) → Polynomial F)
    (hsum : ∑ i, h i = h₁)
    (hgcd : ∀ q : Polynomial F, (∀ i, q ∣ h i) → IsUnit q)
    (hdeg₁ : h₁.natDegree ≤ D) (hdeg : ∀ i, (h i).natDegree ≤ D)
    (hnonconst : 0 < h₁.natDegree ∨ ∃ i, 0 < (h i).natDegree)
    (hsubsum : ∀ T : Finset (Fin (r - 1)), T.Nonempty → ∑ i ∈ T, h i ≠ 0)
    (hli : LinearIndependent F h) :
    h₁.natDegree < (r - 2) * (numDistinctRoots h₁ + ∑ i, numDistinctRoots (h i)) := by
  sorry

end SumsHighPowers.PITLifting
