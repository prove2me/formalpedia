-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P48_dilation_threshold
-- name    : QAlgorithms.Papers.Independent.Information100.P48.dilation_threshold
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T11:45:08.669706+00:00
-- url     : https://prove2.me/theorems/e4b89a14-c247-4e37-8b00-e3e19e8470dc
-- title:
--   Shared-dilation success, CHSH and exact activation boundary
-- statement:
--   Let $\gamma\in[0,1]$. Coherently control the principal-angle ADC dilation and its inverse on one clean environmental qubit, using control input $|+\rangle$ and selected Hadamard outcome $+$. Start the system in $I/2$ and use $X,Y,(X+Y)/\sqrt2,(X-Y)/\sqrt2$. Then
--
--   $$
--   p^D_+=1-\frac\gamma2>0,\qquad S_T^D=\frac{4\sqrt{2-2\gamma}}{2-\gamma}.
--   $$
--
--   Let $\gamma_D=2(\sqrt2-1)$. Strict violation is equivalent to $\gamma<\gamma_D$, and activation over the nonviolating deterministic baseline is equivalent to $1/2\le\gamma<\gamma_D$. Moreover, $4\sqrt{10}-12<\gamma_D$. This is the larger fixed-equatorial activation region; it is not an optimization over arbitrary dilations.
-- source:
--   Coherent Control of Channel Dilations Activate Temporal Bell Nonclassicality, arXiv:2607.05643v1, PDF p. 9, §IV Eq.(54): equivalent-dilation CHSH, success and exact activation threshold

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P48

namespace QAlgorithms.Papers.Independent.Information100.P48

open scoped Matrix ComplexConjugate

noncomputable section

/-- §IV, PDF pp.8–9, Eq.(54): shared forward/inverse equatorial threshold.
This is a fixed-setting result, not a claim of optimality over all dilations. -/
theorem dilation_threshold (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) :
    success (sharedADC g false) = 1 - g / 2 ∧
    0 < success (sharedADC g false) ∧
    temporal (sharedADC g false) = 4 * Real.sqrt (2 - 2 * g) / (2 - g) ∧
    (2 < temporal (sharedADC g false) ↔ g < sharedCritical) ∧
    (g ∈ activation (fun t => sharedADC t false) ↔ 1 / 2 ≤ g ∧ g < sharedCritical) ∧
    independentCritical < sharedCritical := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P48
