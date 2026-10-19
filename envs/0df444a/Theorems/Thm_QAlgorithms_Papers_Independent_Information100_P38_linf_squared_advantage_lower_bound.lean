-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P38_linf_squared_advantage_lower_bound
-- name    : QAlgorithms.Papers.Independent.Information100.P38.linf_squared_advantage_lower_bound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T11:08:49.419675+00:00
-- url     : https://prove2.me/theorems/ff929e00-944f-4c1e-8e97-d915e3e4c996
-- title:
--   Theorem 4 / Eq.(41)
-- statement:
--   Let $d\ge2$, let $M$ be a POVM with a positive finite number of outcomes, and let $H$ have weakly increasing real energies. Put $g_{\min}=\min_{1\le k<d}(E_k-E_{k-1})$ and $C_{\ell_\infty}(M)=\max_{i<j}\sum_\mu|(M_\mu)_{ij}|$. Then
--
--   $$A_H^M\ge\frac{g_{\min}}{d^2}\,[C_{\ell_\infty}(M)]^2.$$
--
--   The dimension assumption makes both indexing sets nonempty. Vanishing gaps are allowed in this inequality. This gives a quantitative work-advantage guarantee from off-diagonal measurement entries.
-- source:
--   All coherent measurements provide observational ergotropic advantage, arXiv:2609.18735v1, PDF p. 8, Theorem 4 / Eq.(41)

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P38

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P38

open scoped ComplexConjugate Matrix

/-- Paper p.8, Theorem 4, Eq.(41): square of l-infinity coherence divided by d squared;
d ≥ 2 ensures both the off-diagonal and adjacent-gap indexing sets are nonempty. -/
theorem linf_squared_advantage_lower_bound {d n : ℕ} (hd : 2 ≤ d) (hn : 0 < n)
    (E : Fin d → ℝ) (hE : Monotone E)
    (M : Fin n → Matrix (Fin d) (Fin d) ℂ) (hM : IsPOVM M) :
    minimumAdjacentEnergyGap E / (d : ℝ)^2 * (measurementLinfCoherence M)^2 ≤
      observationalAdvantage E M := by sorry

end QAlgorithms.Papers.Independent.Information100.P38

end
