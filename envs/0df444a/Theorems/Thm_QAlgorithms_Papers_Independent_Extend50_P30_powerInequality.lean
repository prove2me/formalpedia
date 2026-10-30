-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P30_powerInequality
-- name    : QAlgorithms.Papers.Independent.Extend50.P30.powerInequality
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:27:38.808992+00:00
-- url     : https://prove2.me/theorems/694aff37-cb30-4abf-a34a-dfa49a3e6560
-- title:
--   The real power inequality
-- statement:
--   Let $k\geq1$ be real and $p\in[0,1]$. If $4p^k-3\geq0$, then the inequality below holds. The right-side hypothesis forces $p\geq3/4$, so both real-power bases in the conclusion have their intended nonnegative values.
--
--   $$
--   (4p-3)^k\geq4p^k-3.
--   $$
--
--   This gives the source's the real power inequality in the fixed computational-basis and phase conventions.
--
--   **Formalization Note** Pure states carry norm one; stabilizer averages use density matrices to discard global phases. All finite tensor indices are explicitly ordered by copy, then physical qudit.
-- source:
--   Schur-Weyl Duality for the Clifford Group with Applications: Property Testing, a Robust Hudson Theorem, and de Finetti Representations, arXiv:1712.08628v3, PDF p. 57, lemma-7.4

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P30

noncomputable section

open scoped BigOperators ComplexConjugate Matrix

namespace QAlgorithms.Papers.Independent.Extend50.P30

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

open QAlgorithms.Papers.Independent.Gap20.P06 (ketBra)

attribute [local instance] Classical.propDecidable

/-- PDF p.57, Lemma 7.4: real k>=1 and nonnegative right-hand side are both retained. -/
theorem powerInequality (k p : ℝ) (hk : 1 ≤ k) (hp : p ∈ Set.Icc 0 1)
    (hrhs : 0 ≤ 4 * Real.rpow p k - 3) :
    4 * Real.rpow p k - 3 ≤ Real.rpow (4 * p - 3) k := by sorry

end QAlgorithms.Papers.Independent.Extend50.P30

end
