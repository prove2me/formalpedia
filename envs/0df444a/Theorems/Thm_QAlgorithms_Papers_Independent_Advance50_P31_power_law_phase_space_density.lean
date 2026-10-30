-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P31_power_law_phase_space_density
-- name    : QAlgorithms.Papers.Independent.Advance50.P31.power_law_phase_space_density
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:13:31.213992+00:00
-- url     : https://prove2.me/theorems/d69dc241-bfee-4991-891c-d5246003ba5d
-- title:
--   Power-law density derived from classical phase-space volume
-- statement:
--   Let $d\ge1$ be an integer and let $\gamma,m>0$. On momentum-position phase space $\mathbb R^d\times\mathbb R^d$, equipped with ordinary Lebesgue volume $\lambda_{2d}$, construct $h(p,x)=\|p\|^2/(2m)+\|x\|^\gamma$ and put $a=d/\gamma+d/2$. Then $h$ is measurable and there exists a constant $A>0$, determined by these physical parameters, such that its pushforward energy measure has density $A\epsilon^{a-1}$ on positive energies and zero density elsewhere: $$h_*\lambda_{2d}(d\epsilon)=\mathbf 1_{\{\epsilon>0\}}A\epsilon^{a-1}\,d\epsilon.$$ This supplies the actual semiclassical density used by the companion moment theorem, without identifying it with a discrete counting measure.
-- source:
--   Capacities of noiseless quantum channels for massive indistinguishable particles: Bosons vs. fermions, arXiv:quant-ph/0512200v3, PDF p. 14, §IX, Eqs.(83)–(86)

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P31

noncomputable section

open MeasureTheory

open scoped ENNReal BigOperators

namespace QAlgorithms.Papers.Independent.Advance50.P31

open QAlgorithms.Papers.Independent.Dependency50.P13 (IsTraceClass operatorTrace)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {I : Type*} [Countable I]

/-- PDF p.14, Eqs.(83)--(86): the semiclassical energy density is derived from
phase-space volume, rather than posited as a power function. The pushforward
formulates the source's delta-function integral without distributional notation.
Its normalization A is constructed from d, gamma and m. The density vanishes on
nonpositive energies; no exact discrete spectral counting identity is asserted. -/
theorem power_law_phase_space_density
    (d : ℕ) (hd : 0 < d) (gamma m : ℝ)
    (hgamma : 0 < gamma) (hm : 0 < m) :
    ∃ A : ℝ, 0 < A ∧ Measurable (powerLawPhaseSpaceEnergy d gamma m) ∧
      Measure.map (powerLawPhaseSpaceEnergy d gamma m) volume =
        volume.withDensity (fun energy : ℝ => ENNReal.ofReal
          (if 0 < energy then densityOfStates A (trapExponent d gamma) energy else 0)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P31

end
