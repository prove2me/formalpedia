-- Prove2me | Theorems.Thm_SumsHighPowers_PITLifting_theorem_2_7_of_not_linearIndependent
-- name    : SumsHighPowers.PITLifting.theorem_2_7_of_not_linearIndependent
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-11T21:14:01.405956+00:00
-- url     : https://prove2.me/theorems/c638df9f-42d9-4303-acd7-a55902900705
-- title:
--   Theorem 2.7, linearly dependent case — deg h₁ < (r − 2) Σ ν(hᵢ) when h₂, …, h_r are dependent
-- statement:
--   Let $D, r \in \mathbb N$ with $r \ge 2$, and let $F$ be a field of characteristic $0$ or of characteristic $p > (r-1)D$. Let $h_1, h_2, \dots, h_r \in F[x]$ satisfy $h_2 + \dots + h_r = h_1$ and $\gcd(h_2, \dots, h_r) = 1$, with $\deg h_i \le D$ for all $i$, not all $h_i$ constant, no nonempty subsum of $h_2, \dots, h_r$ vanishing, and **$h_2, \dots, h_r$ linearly dependent over $F$**. Then
--   $$\deg h_1 < (r-2)\sum_{i=1}^{r} \nu(h_i),$$
--   where $\nu(h)$ is the number of distinct roots of $h$ in the algebraic closure of $F$ (`numDistinctRoots`).
--
--   This is the case of `SumsHighPowers.PITLifting.theorem_2_7` (Theorem 2.7 of the mission *PIT and Reconstruction for Sums of High Powers*, p. 18, cited there from Vaserstein–Wheland, Theorem 2.2(a)) in which $h_2, \dots, h_r$ are linearly dependent. Together with `SumsHighPowers.PITLifting.theorem_2_7_of_linearIndependent`, the independent case, it gives Theorem 2.7. In the Lean statement, $h_2, \dots, h_r$ are `h 0, …, h (r − 2)`, the gcd condition says that every common divisor of them is a unit, and every binder is the one in `theorem_2_7`, plus the hypothesis `hdep : ¬ LinearIndependent F h`. The hypotheses force $r \ge 3$: for $r = 2$ the single $h_2$ is nonzero and therefore independent.
--
--   Vaserstein and Wheland (*Vanishing polynomial sums*, Comm. Algebra 31(2) (2003) 751–772, https://doi.org/10.1081/AGB-120017341) treat this case in their §4, for characteristic $0$. Their argument splits the family into a maximal irreducible subfamily $I_1$ and its complement $I_2$. It then bounds the degree of $z_1 = \gcd(I_1)$ through the minimal relation between $z \in \operatorname{span} I_1 \cap \operatorname{span} I_2$ and the members of $I_2$. The root count in that step has to handle points where $z$ and a member of $I_2$ both vanish but no member of $I_1$ does.
-- source:
--   PIT and Reconstruction for Sums of High Powers (STOC 2027 submission 1653), §2.3, p. 18, Theorem 2.7 in the case where h_2, …, h_r are linearly dependent, cited there from Vaserstein, L. N. and Wheland, E. R., Vanishing polynomial sums, Comm. Algebra 31(2) (2003) 751–772, https://doi.org/10.1081/AGB-120017341, Theorem 2.2(a) (the dependent case is its Theorem 4.4 / Corollary 4.7)

import Mathlib
import Definitions.Def_SumsHighPowers_PITLifting_numDistinctRoots

namespace SumsHighPowers.PITLifting

theorem theorem_2_7_of_not_linearIndependent {F : Type*} [Field F] (D r : ℕ) (hr : 2 ≤ r)
    (hchar : ringChar F = 0 ∨ (r - 1) * D < ringChar F)
    (h₁ : Polynomial F) (h : Fin (r - 1) → Polynomial F)
    (hsum : ∑ i, h i = h₁)
    (hgcd : ∀ q : Polynomial F, (∀ i, q ∣ h i) → IsUnit q)
    (hdeg₁ : h₁.natDegree ≤ D) (hdeg : ∀ i, (h i).natDegree ≤ D)
    (hnonconst : 0 < h₁.natDegree ∨ ∃ i, 0 < (h i).natDegree)
    (hsubsum : ∀ T : Finset (Fin (r - 1)), T.Nonempty → ∑ i ∈ T, h i ≠ 0)
    (hdep : ¬ LinearIndependent F h) :
    h₁.natDegree < (r - 2) * (numDistinctRoots h₁ + ∑ i, numDistinctRoots (h i)) := by
  sorry

end SumsHighPowers.PITLifting
