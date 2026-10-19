-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P04_negativityLowerBound
-- name    : QAlgorithms.Papers.Independent.Information100.P04.negativityLowerBound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:30:06.642953+00:00
-- url     : https://prove2.me/theorems/a1da4161-7aac-4048-b15a-ba33b53fad31
-- title:
--   Quantitative distillation lower bound from negativity
-- statement:
--   Let $\rho$ be a bipartite density matrix on nonzero finite-dimensional systems, set $d=\min(d_A,d_B)$ and $N(\rho)=(\|\rho^{\Gamma_B}\|_1-1)/2$, and let $h_2$ be binary entropy in bits. Then
--
--   $$E_{d,\mathrm{PPT}}(\rho)\ge1-h_2\!\left(\frac12+\frac{N(\rho)}{d+1}\right).$$
--
--   In particular, positive negativity implies a strictly positive PPT distillation rate. At $d=1$, the negativity is zero and the bound is zero. This makes the qualitative NPT distillability statement quantitative.
-- source:
--   On PPT entanglement distillation, arXiv:2610.12454v1, PDF p. 4, negativityLowerBound

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P04

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter Topology

namespace QAlgorithms.Papers.Independent.Information100.P04

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Main quantitative negativity bound, PDF p.4, from (47),(65).
The one-dimensional case has N=0 and gives zero. -/
theorem negativityLowerBound {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A]
    [DecidableEq B] [Nonempty A] [Nonempty B] (rho : Matrix (A × B) (A × B) ℂ)
    (hrho : IsDensityMatrix rho) :
    1-binEntropy2 (1/2 + Entanglement.negativity rho /
      ((min (Fintype.card A) (Fintype.card B) : ℕ) + 1 : ℝ)) ≤ distillable rho ∧
      (0 < Entanglement.negativity rho → 0 < distillable rho) := by sorry

end QAlgorithms.Papers.Independent.Information100.P04

end
