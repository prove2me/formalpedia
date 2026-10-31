-- Prove2me | Theorems.Thm_TSPSDPGap_theorem_4_21
-- name    : TSPSDPGap.theorem_4_21
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:42:02.492897+00:00
-- url     : https://prove2.me/theorems/0c089aab-fef9-4f9b-aece-01dafe286a73
-- title:
--   Theorem 4.21 — the SDP (1) objective of $Y$ on the simplicial instance is $O(1/n)$
-- statement:
--   Let $g\ge2$ be even. There is a constant $\tilde c_g$, depending on $g$ but not on $n$, such that for every $n$ with $g\mid n$ and $g<n$,
--   $$
--   \tfrac12\operatorname{trace}\bigl((D\otimes C_1)Y\bigr)\le\frac{\tilde c_g}{n},
--   $$
--   where $D=(J_g-I_g)\otimes J_{n/g}$ is the simplicial instance on $n$ cities and $Y$ is the solution (3).
--
--   The SDP (1) value of the simplicial instances therefore tends to $0$ while their optimal tour costs $g$.
--
--   **Formalization Note** The constant is quantified before $n$.
--
--   Differences from the source:
--   - encoding: standing assumptions of §4: g even, g groups of n/g vertices, a_i and b_i with denominators g, g − 1, n − g → hypotheses Even g, 2 ≤ g, g ∣ n, g < n; reason: the section's standing assumption (g even) plus the conditions under which (3) and a_i, b_i are defined; given g ∣ n they exclude only n/g ∉ ℕ, g ∈ {0, 1} and n − g = 0
--   - encoding: Y = 1/(2n)[(J_g − I_g) ⊗ J_{n/g} ⊗ B + I_g ⊗ J_{n/g} ⊗ A + I_g ⊗ I_{n/g} ⊗ (2I_n − A)] (3) → Ymat g n, entrywise: block (p, q) is (1/(2n))·2I_n if p = q, (1/(2n))A if p ≠ q lie in the same group ⌊p/(n/g)⌋, (1/(2n))B otherwise; reason: equal to (3) reindexed by Fin g × Fin (n/g) ≃ Fin n (proved: Solutions/verification/TSPSDPGap_sanity.lean, Ymat_eq_eq3); same matrix
--   - encoding: D = (J_g − I_g) ⊗ J_{n/g} → simplicialCost g n (cost 0 iff ⌊p/(n/g)⌋ = ⌊q/(n/g)⌋); reason: equal to the Kronecker form reindexed by Fin g × Fin (n/g) ≃ Fin n (proved: Solutions/verification/TSPSDPGap_sanity.lean); same matrix
-- source:
--   Gutekunst & Williamson, SDP Relaxations of the TSP and Their Integrality Gaps, arXiv:1907.09054v1, Theorem 4.21, p.26

import Mathlib
import Definitions.Def_TSPSDPGap_sdp1Objective
import Definitions.Def_TSPSDPGap_simplicialCost
import Definitions.Def_TSPSDPGap_Ymat

namespace TSPSDPGap

/-- **Theorem 4.21: the SDP (1) objective of `Y` on the simplicial instance is `O(1/n)`.**
Gutekunst & Williamson, *SDP Relaxations of the TSP and Their Integrality Gaps*,
arXiv:1907.09054v1, Theorem 4.21, p.26:
"For Y as above, there exists a constant c̃_g (depending on g but not n) such that
½ trace((D ⊗ C_1)Y) ≤ c̃_g/n."

Here `D = (J_g − I_g) ⊗ J_{n/g}` is the simplicial instance (p.14). For every even `g ≥ 2`
there is one constant `c`, chosen before `n`, such that for every `n` with `g ∣ n` and `g < n`,
`½ trace((D ⊗ C^(n)_1) Y) ≤ c / n`.

**Formalization Note.** `D = simplicialCost g n`, `Y = Ymat g n`, the objective is
`sdp1Objective`. The existential `∃ c` precedes `∀ n`, so `c` depends on `g` only. Standing
hypotheses as in §4 (`g` even, `2 ≤ g`, `g ∣ n`, `g < n`). -/
theorem theorem_4_21 (g : ℕ) (hg : Even g) (hg2 : 2 ≤ g) :
    ∃ c : ℝ, ∀ n : ℕ, g ∣ n → g < n →
      sdp1Objective n (simplicialCost g n) (Ymat g n) ≤ c / n := by sorry

end TSPSDPGap
