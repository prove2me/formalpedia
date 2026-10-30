-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P20_multiplicity_ratio_one_step
-- name    : QAlgorithms.Papers.Independent.Extend50.P20.multiplicity_ratio_one_step
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:10:45.39482+00:00
-- url     : https://prove2.me/theorems/712a3bda-a71e-40f6-895d-b8bc2deb493d
-- title:
--   One-step squared-multiplicity ratio
-- statement:
--   Let $d\ge1$ and $N\ge1$. Put $S_r=\sum_{\lambda\vdash r,\,h(\lambda)\le d}m_\lambda^2$, with $m_\lambda$ the actual multiplicity in the tensor-factor permutation action of $S_r$ on $(\mathbb C^d)^{\otimes r}$. Then
--
--   $$\frac{S_N}{S_{N-1}}=\frac{d^2+N-1}{N}.$$
--
--   At $N=1$ this is $S_1/S_0=d^2$, since the empty-degree sum is one. The proposition gives the separately numbered one-step recurrence.
-- source:
--   Optimal Multi-port-based Teleportation Schemes, arXiv:2011.09256v3, PDF p. 23, Proposition 13 / Eq. (113)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P20

noncomputable section

open scoped BigOperators Matrix ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Extend50.P20

attribute [local instance] Classical.propDecidable

/-- Proposition 13, PDF p.23, Eq.(113). N>=1 prevents division by zero and
N-1 is the actual preceding tensor degree, including the empty degree at N=1. -/
theorem multiplicity_ratio_one_step (d N : ℕ) (hd : 0 < d) (hN : 1 ≤ N) :
    multiplicitySquares d N / multiplicitySquares d (N-1) =
      ((d : ℝ)^2+(N : ℝ)-1)/(N : ℝ) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P20

end
