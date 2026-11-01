-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P98_rankOne_domination_iff_inversePairing
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P98.rankOne_domination_iff_inversePairing
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:57:27.033124+00:00
-- url     : https://prove2.me/theorems/8eeefe15-fad6-4d6a-a741-ebfb9d4ada5f
-- title:
--   Rank-one domination and inverse pairing
-- statement:
--   Let $Y=\mathbb C^m$, $Z=\mathbb C^r$, $m,r\ge1$, and let $v\in Y\otimes Z$ be any vector. For every positive definite operator $H\in L(Z)$,
--   $$
--   I_Y\otimes H\succeq vv^*\quad\Longleftrightarrow\quad\operatorname{Re}\operatorname{Tr}\big((\operatorname{Tr}_Y vv^*)^*H^{-1}\big)\le1.
--   $$
--   No normalization of $v$ is required, and positive definiteness ensures the inverse is the ordinary inverse. This equivalence converts a rank-one operator constraint into a scalar constraint for the fidelity dual program.
-- source:
--   Semidefinite programs for completely bounded norms, arXiv:0901.4709v2, PDF p. 14, Proposition 8 (rank-one domination and inverse pairing)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P98

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intakenext100.P98

/-- PDF p.14, Proposition 8: positive definiteness guards the inverse. At v=0
both conditions hold. The proposition needs no correction to its statement. -/
theorem rankOne_domination_iff_inversePairing {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (v : EuclideanSpace ℂ (Fin m × Fin r)) (Z : (Matrix (Fin r) (Fin r) ℂ)) (hZ : Z.PosDef) :
    (unitTensor m Z - pureDensity v).PosSemidef ↔
      realTracePairing (traceLeft (pureDensity v)) Z⁻¹ ≤ 1 := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P98

end
