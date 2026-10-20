-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P48_independent_threshold
-- name    : QAlgorithms.Papers.Independent.Information100.P48.independent_threshold
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T11:44:36.215384+00:00
-- url     : https://prove2.me/theorems/0003b95e-e85b-46e5-8ba4-f0270df88701
-- title:
--   Independent-control success, CHSH and exact activation boundary
-- statement:
--   Let $\gamma\in[0,1]$. Use two identical principal-angle ADC dilations on independent clean qubit environments, control input $|+\rangle$, and selected Hadamard outcome $+$. Start the system in $I/2$ and use $X,Y,(X+Y)/\sqrt2,(X-Y)/\sqrt2$. The true success probability and conditional temporal CHSH value are
--
--   $$
--   p^{\rm ind}_+=1-\frac\gamma4>0,\qquad S_T^{\rm ind}=\frac{8\sqrt{2-2\gamma}}{4-\gamma}.
--   $$
--
--   Writing $\gamma_{\rm ind}=4\sqrt{10}-12$, strict violation holds exactly when $\gamma<\gamma_{\rm ind}$. Activation relative to a nonviolating deterministic ADC holds exactly for $1/2\le\gamma<\gamma_{\rm ind}$. This makes the source's approximate crossing precise while retaining its fixed measurement settings.
-- source:
--   Coherent Control of Channel Dilations Activate Temporal Bell Nonclassicality, arXiv:2607.05643v1, PDF p. 9, §IV Eq.(53): independent-control CHSH, success and exact activation threshold

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P48

namespace QAlgorithms.Papers.Independent.Information100.P48

open scoped Matrix ComplexConjugate

noncomputable section

/-- §IV, PDF pp.6,9, Eq.(53): fixed equatorial CHSH, true success and exact crossing.
The rounded 0.65 is replaced by the root of the displayed formula. -/
theorem independent_threshold (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) :
    success (independentADC g false) = 1 - g / 4 ∧
    0 < success (independentADC g false) ∧
    temporal (independentADC g false) = 8 * Real.sqrt (2 - 2 * g) / (4 - g) ∧
    (2 < temporal (independentADC g false) ↔ g < independentCritical) ∧
    (g ∈ activation (fun t => independentADC t false) ↔
      1 / 2 ≤ g ∧ g < independentCritical) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P48
