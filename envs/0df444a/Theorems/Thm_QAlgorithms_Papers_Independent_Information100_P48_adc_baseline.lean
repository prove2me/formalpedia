-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P48_adc_baseline
-- name    : QAlgorithms.Papers.Independent.Information100.P48.adc_baseline
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T11:40:49.670214+00:00
-- url     : https://prove2.me/theorems/2d568474-8980-4753-9203-3275395f24bd
-- title:
--   Deterministic ADC temporal CHSH and exact baseline threshold
-- statement:
--   Let $\gamma\in[0,1]$. Start the system qubit in $I/2$, apply the ADC between two rank-one projective measurements, and use $X,Y,(X+Y)/\sqrt2,(X-Y)/\sqrt2$. With $S_T=C_{11}+C_{12}+C_{21}-C_{22}$, the normalized temporal correlators give
--
--   $$
--   S_T(\gamma)=2\sqrt{2(1-\gamma)},\qquad S_T(\gamma)>2\ \Longleftrightarrow\ \gamma<\tfrac12.
--   $$
--
--   The value is nonincreasing on $[0,1]$. This is the deterministic benchmark for post-selected activation; the crossing itself is not a violation.
-- source:
--   Coherent Control of Channel Dilations Activate Temporal Bell Nonclassicality, arXiv:2607.05643v1, PDF p. 3, §II B: deterministic ADC temporal-CHSH value and threshold

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P48

namespace QAlgorithms.Papers.Independent.Information100.P48

open scoped Matrix ComplexConjugate

noncomputable section

/-- §II B, PDF p.3: deterministic equatorial value, monotonicity and strict threshold. -/
theorem adc_baseline (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) :
    temporal (adc g) = 2 * Real.sqrt (2 * (1 - g)) ∧
    (2 < temporal (adc g) ↔ g < 1 / 2) ∧
    AntitoneOn (fun t => temporal (adc t)) (Set.Icc (0 : ℝ) 1) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P48
