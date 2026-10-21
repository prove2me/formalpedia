-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P21_haar_low_count_proportion
-- name    : QAlgorithms.Papers.Independent.Next46.P21.haar_low_count_proportion
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T18:41:24.140771+00:00
-- url     : https://prove2.me/theorems/00ddbccc-f679-4ceb-b0de-86ac39cdcb96
-- title:
--   Haar proportion of operators admitting short approximations
-- statement:
--   For the same ancilla-free discrete-phase one-qubit Clifford+T gate set, there exist absolute real constants $K$, $A>0$ and $\varepsilon_0>0$ such that $K$ satisfies the worst-case slope-three bound and, for every normalized Haar probability measure $\mu$ on $SU(2)$, every $0<\varepsilon\le\varepsilon_0$ and every integer deficit $r\ge0$,
--
--   $$
--   \mu\{U\in SU(2):\exists c,\ T(c)\le K+3\log_2(1/\varepsilon)-r,\ \|U_c-U\|_{\mathrm{op}}\le\varepsilon\}\le A\,2^{-r}.
--   $$
--
--   The word $c$ is an arbitrary finite chronological list of $H,S,T,\omega I$ gates; its determinant need not be $1$. Its T-count is the number of T instructions. Spectral error includes global phase. The constants precede both the accuracy and the deficit. The shared worst-case property is $\forall\eta>0\ \exists V\in SU(2)$ such that every word within $\eta$ of $V$ has T-count at least $K+3\log_2(1/\eta)$. This quantifies the source's claim that most operators are close to the lower bound.
-- source:
--   Efficient Clifford+T approximation of single-qubit operators, arXiv:1212.6253v2, PDF p. 13, §9 following (36): Haar proportion bound

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P21

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P21

open Set

open scoped ComplexConjugate

/-- Section 9 following (36), PDF p.13: normalized Haar proportion with uniform constants.
The same additive K also satisfies the preceding worst-case lower bound. -/
theorem haar_low_count_proportion :
    ∃ K A eps0 : ℝ, 0 < A ∧ 0 < eps0 ∧ WorstCaseBound K ∧
      ∀ mu : MeasureTheory.Measure (Matrix.specialUnitaryGroup Bool ℂ),
        MeasureTheory.IsProbabilityMeasure mu → MeasureTheory.Measure.IsHaarMeasure mu →
        ∀ eps : ℝ, 0 < eps → eps ≤ eps0 → ∀ deficit : ℕ,
          mu (lowCountEvent K eps deficit) ≤ ENNReal.ofReal (A / (2 : ℝ) ^ deficit) := by sorry

end QAlgorithms.Papers.Independent.Next46.P21

end
