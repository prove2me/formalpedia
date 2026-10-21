-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P44_infiniteBandWaveform
-- name    : QAlgorithms.Papers.Independent.Renew46.P44.infiniteBandWaveform
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T21:44:25.552984+00:00
-- url     : https://prove2.me/theorems/ce84fdca-1904-4820-9b82-ed29230b3485
-- title:
--   §V.4, (141)–(144): infinite-band periodic waveform capacity
-- statement:
--   Let $\hbar>0$, finite power $E\ge0$, and continuous nonnegative $N(\omega)$ on $\omega>0$ be given. For each positive real $T$, retain only the finitely many positive periodic grid frequencies between positive cutoffs $\omega_-(T)<\omega_+(T)$, with the lower cutoff decreasing to zero and the upper cutoff increasing to infinity. Use the same finite-mode operational coding model and energy $TE$. At $E=0$ capacity is zero. At $E>0$ there is $\theta>0$ for which
--
--   $$m_*(\omega)=\left((e^{\theta\hbar\omega}-1)^{-1}-N(\omega)\right)_+,\qquad
--   \frac1{2\pi}\int_0^\infty\hbar\omega m_*(\omega)d\omega=E.$$
--
--   For every measurable nonnegative allocation $m$ of finite energy at most $E$, the entropy difference is integrable, and
--
--   $$\frac1{2\pi}\int_0^\infty[g(N+m)-g(N)]d\omega\le
--   \frac1{2\pi}\int_0^\infty[g(N+m_*)-g(N)]d\omega=C,
--   \qquad \lim_{T\to\infty}\frac{C_T}{T}=C.$$
--
--   The maximum is attained by $m_*$, and $C$ equals operational waveform capacity. Individual total noise entropy and energy need not be finite. The statement integrates the difference and does not form infinity minus infinity.
-- source:
--   Coding Theorems for Quantum Channels, arXiv:quant-ph/9809023v1, PDF p. 34, §V.4, (141)–(144): infinite-band periodic waveform capacity

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

/-- Infinite-band continuation, PDF pp.34-36, (141)-(144).
This is a limit of finite-T coding problems. No finite total noise entropy or
energy is imposed; the integrable entropy difference has an attained maximum. -/
theorem infiniteBandWaveform (hbar E : ℝ) (N : ℝ → ℝ) (windows : FrequencyWindows)
    (hhbar : 0 < hbar) (hE : 0 ≤ E)
    (hN : ∀ omega, 0 < omega → 0 ≤ N omega)
    (hcontinuous : ContinuousOn N (Set.Ioi 0)) :
    (E = 0 → waveformCapacity hbar N windows.low windows.high E = 0) ∧
    (0 < E → ∃ theta : ℝ, 0 < theta ∧
      FeasibleSpectrum hbar E (spectralAllocation hbar theta N) ∧
      (∫ omega in Set.Ioi (0 : ℝ),
        hbar * omega * spectralAllocation hbar theta N omega) / (2 * Real.pi) = E ∧
      (∀ m : ℝ → ℝ, FeasibleSpectrum hbar E m →
        Integrable (fun omega => g (N omega + m omega) - g (N omega))
          (volume.restrict (Set.Ioi 0)) ∧
        spectralInformation N m ≤ spectralInformation N (spectralAllocation hbar theta N)) ∧
      waveformCapacity hbar N windows.low windows.high E =
        ENNReal.ofReal (spectralInformation N (spectralAllocation hbar theta N)) ∧
      Tendsto (fun T : ℝ => waveformInformation hbar N (windows.low T) (windows.high T) E T / T)
        atTop (nhds (spectralInformation N (spectralAllocation hbar theta N)))) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P44

end
