-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P44_finiteModeWaterFilling
-- name    : QAlgorithms.Papers.Independent.Renew46.P44.finiteModeWaterFilling
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T21:42:38.259988+00:00
-- url     : https://prove2.me/theorems/17603934-def0-422b-8a3a-1911bcf83223
-- title:
--   Proposition 3: finite multimode Gaussian water filling
-- statement:
--   Let a finite set of modes have frequencies $\omega_j>0$, noise occupations $N_j\ge0$, and $\hbar>0$. Use the joint displaced thermal output $\bigotimes_jD(z_j)\tau_{N_j}D(z_j)^\dagger$ and transmitted modulation cost $\sum_j\hbar\omega_j|z_j|^2$, with finite budget $E\ge0$. At $E=0$, operational capacity is zero. For $E>0$ assume the mode set is nonempty. Then there exists $\theta>0$ such that
--
--   $$N_j(\theta)=\frac1{e^{\theta\hbar\omega_j}-1},\quad m_j^*=(N_j(\theta)-N_j)_+,\quad
--   \sum_j\hbar\omega_jm_j^*=E,$$
--
--   and
--
--   $$C=\sum_j\bigl(g(N_j(\theta))-g(N_j)\bigr)_+.$$
--
--   The product of circular Gaussian priors of variances $m_j^*$ attains this capacity; zero variances are Dirac factors. Active factors have density $(\pi m_j^*)^{-1}e^{-|z_j|^2/m_j^*}$, restoring the missing normalization in printed (109). No finite water level is required at zero energy.
-- source:
--   Coding Theorems for Quantum Channels, arXiv:quant-ph/9809023v1, PDF p. 29, Proposition 3: finite multimode Gaussian water filling

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P44

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P44

open Filter MeasureTheory

open scoped ENNReal NNReal Topology BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

open QAlgorithms.Papers.Independent.Claimed50.P16 (tracePair)

open QAlgorithms.Papers.Independent.Frontier30.P14 (traceClassTensorPower)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Proposition 3, PDF pp.28-30, (107)-(111): finite-mode operational capacity,
energy equation, and normalized attaining distribution. At E=0 no nonexistent
finite water level is required. Formula (109) is corrected by its probability
normalizers (pi m_j)^(-1) for active modes; inactive modes are Dirac. -/
theorem finiteModeWaterFilling {J : Type} [Fintype J]
    (hbar E : ℝ) (omega N : J → ℝ)
    (hhbar : 0 < hbar) (homega : ∀ j, 0 < omega j)
    (hN : ∀ j, 0 ≤ N j) (hE : 0 ≤ E) (hmode : 0 < E → Nonempty J) :
    (E = 0 → averageErrorCqCapacity (multimodeOutput N) (modeCost hbar omega) E = 0) ∧
    (0 < E → ∃ theta : ℝ, 0 < theta ∧
      (∑ j, hbar * omega j * waterfill hbar theta omega N j) = E ∧
      averageErrorCqCapacity (multimodeOutput N) (modeCost hbar omega) E =
        ENNReal.ofReal (∑ j, max (g (planck hbar theta (omega j)) - g (N j)) 0) ∧
      IsProbabilityMeasure (modeLaw (waterfill hbar theta omega N)) ∧
      Integrable (modeCost hbar omega) (modeLaw (waterfill hbar theta omega N)) ∧
      (∫ z, modeCost hbar omega z ∂modeLaw (waterfill hbar theta omega N)) = E ∧
      integralChi (multimodeOutput N) (modeLaw (waterfill hbar theta omega N)) =
        averageErrorCqCapacity (multimodeOutput N) (modeCost hbar omega) E) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P44

end
