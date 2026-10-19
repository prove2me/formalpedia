-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P38_coherence_robustness_advantage_bound
-- name    : QAlgorithms.Papers.Independent.Information100.P38.coherence_robustness_advantage_bound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T11:07:52.078115+00:00
-- url     : https://prove2.me/theorems/da8def7f-ca76-4364-aaa4-10078bf7fc3a
-- title:
--   Theorem 3 / Eq.(35)
-- statement:
--   Let $d,n\ge1$, let $M$ be an $n$-outcome POVM, and let $H$ have weakly increasing real energies. Define $R_C(M)$ as the minimum $r\ge0$ such that $(M+rP)/(1+r)$ is incoherent for some $n$-outcome POVM $P$. Then
--
--   $$A_H^M\le\frac{d-1}{d}(E_{d-1}-E_0)R_C(M).$$
--
--   The minimum defining robustness is finite and attained for every finite POVM; feasibility is not an additional assumption. The fraction uses real arithmetic, including $d=1$. This quantitatively bounds accessible work advantage in terms of measurement coherence.
-- source:
--   All coherent measurements provide observational ergotropic advantage, arXiv:2609.18735v1, PDF p. 7, Theorem 3 / Eq.(35)

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P38

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P38

open scoped ComplexConjugate Matrix

/-- Paper p.7, Theorem 3, Eq.(35): robustness upper bound, with real (d-1)/d. -/
theorem coherence_robustness_advantage_bound {d n : ℕ} (hd : 0 < d) (hn : 0 < n)
    (E : Fin d → ℝ) (hE : Monotone E)
    (M : Fin n → Matrix (Fin d) (Fin d) ℂ) (hM : IsPOVM M) :
    observationalAdvantage E M ≤ ((d : ℝ) - 1) / (d : ℝ) *
      (E ⟨d - 1, by omega⟩ - E ⟨0, hd⟩) * measurementCoherenceRobustness M := by sorry

end QAlgorithms.Papers.Independent.Information100.P38

end
