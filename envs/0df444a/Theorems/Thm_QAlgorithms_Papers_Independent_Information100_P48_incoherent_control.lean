-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P48_incoherent_control
-- name    : QAlgorithms.Papers.Independent.Information100.P48.incoherent_control
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T11:44:02.478156+00:00
-- url     : https://prove2.me/theorems/7fe869f1-e295-43a5-ba46-c26ccf513e89
-- title:
--   Incoherent selection preserves the deterministic ADC threshold
-- statement:
--   Let $\gamma\in[0,1]$. Prepare the control in $I/2$ and measure either Hadamard outcome after controlling either two independent ADC dilations or shared forward/inverse dilations. In both implementations, on every input operator $R$,
--
--   $$
--   \Phi^{\rm inc}_\pm(R)=\tfrac12\mathcal E_\gamma(R).
--   $$
--
--   For every density input the selected outcome has probability $1/2$, and its normalized output is exactly $\mathcal E_\gamma(\rho)$. Consequently, for system input $I/2$ and settings $X,Y,(X+Y)/\sqrt2,(X-Y)/\sqrt2$, both outcomes in both implementations have
--
--   $$
--   S_T=2\sqrt{2(1-\gamma)}>2\quad\Longleftrightarrow\quad\gamma<1/2.
--   $$
--
--   Thus incoherent control does not enlarge the deterministic violation range.
-- source:
--   Coherent Control of Channel Dilations Activate Temporal Bell Nonclassicality, arXiv:2607.05643v1, PDF p. 5, §III A–B: incoherent control cannot enlarge the ADC violation range

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P48

namespace QAlgorithms.Papers.Independent.Information100.P48

open scoped Matrix ComplexConjugate

noncomputable section

/-- §III A–B, PDF pp.5,6,8: either incoherent outcome is half the deterministic
ADC, with success 1/2 on every density input and unchanged temporal threshold. -/
theorem incoherent_control (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) :
    (∀ (rho : QOp) (minus : Bool),
      incoherentIndependent g minus rho = (1 / 2 : ℂ) • adc g rho ∧
      incoherentShared g minus rho = (1 / 2 : ℂ) • adc g rho) ∧
    (∀ rho : QOp, IsDensityMatrix rho → ∀ minus : Bool,
      (incoherentIndependent g minus rho).trace.re = 1 / 2 ∧
      (incoherentShared g minus rho).trace.re = 1 / 2 ∧
      normalize (incoherentIndependent g minus rho) = adc g rho ∧
      normalize (incoherentShared g minus rho) = adc g rho) ∧
    (∀ minus : Bool,
      temporal (incoherentIndependent g minus) = 2 * Real.sqrt (2 * (1 - g)) ∧
      temporal (incoherentShared g minus) = 2 * Real.sqrt (2 * (1 - g)) ∧
      (2 < temporal (incoherentIndependent g minus) ↔ g < 1 / 2) ∧
      (2 < temporal (incoherentShared g minus) ↔ g < 1 / 2)) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P48
