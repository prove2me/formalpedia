-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P38_projective_coarse_graining_advantage
-- name    : QAlgorithms.Papers.Independent.Information100.P38.projective_coarse_graining_advantage
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T11:05:32.526989+00:00
-- url     : https://prove2.me/theorems/6f1727b1-dfa6-4276-9984-e5c9a142dfdd
-- title:
--   Eq.(21)
-- statement:
--   Let $d,n\ge1$, let $H$ have weakly increasing energies, and let $M_i=|b_i\rangle\langle b_i|$ for an orthonormal basis $(b_i)_{i=0}^{d-1}$. For real coefficients $D_{ji}\ge0$ with $\sum_jD_{ji}=1$, set $M'_j=\sum_iD_{ji}M_i$. Then for every density matrix $\rho$, $E_O(\rho,M')\le E_O(\rho,M)$, and
--
--   $$A_H^{M'}\le A_H^M.$$
--
--   This is monotonicity for post-processing of a rank-one projective starting measurement. It expresses loss of accessible work when its recorded outcomes are blurred.
-- source:
--   All coherent measurements provide observational ergotropic advantage, arXiv:2609.18735v1, PDF p. 5, Eq.(21)

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P38

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P38

open scoped ComplexConjugate Matrix

/-- Paper p.5, Eq.(21): post-processing a rank-one projective measurement cannot
increase the advantage; the pointwise inequality precedes state optimization. -/
theorem projective_coarse_graining_advantage {d n : ℕ} (hd : 0 < d) (hn : 0 < n)
    (E : Fin d → ℝ) (hE : Monotone E)
    (M : Fin d → Matrix (Fin d) (Fin d) ℂ) (hM : rankOneEnergyMeasurement M)
    (D : Fin n → Fin d → ℝ) (hD : ∀ j i, 0 ≤ D j i) (hcol : ∀ i, ∑ j, D j i = 1) :
    (∀ X, IsDensityMatrix X →
      observationalErgotropy E (postprocessedEnergyMeasurement D M) X ≤ observationalErgotropy E M X) ∧
    observationalAdvantage E (postprocessedEnergyMeasurement D M) ≤ observationalAdvantage E M := by sorry

end QAlgorithms.Papers.Independent.Information100.P38

end
