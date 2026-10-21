-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P44_bandLimitedWaveform
-- name    : QAlgorithms.Papers.Independent.Renew46.P44.bandLimitedWaveform
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T21:43:50.256263+00:00
-- url     : https://prove2.me/theorems/54c589cc-9fe8-435e-9543-1b28c1949317
-- title:
--   Proposition 4: band-limited periodic waveform coding capacity
-- statement:
--   Fix $\hbar>0$, finite positive band edges $0<\omega_-<\omega_+$, continuous nonnegative occupation $N$ on that band, and finite signal power $E\ge0$. At observation time $T>0$ use the finite periodic modes $\omega_j=2\pi j/T$ in the band, joint Gaussian outputs, arbitrary collective sub-POVMs, and a separate total signal energy bound $TE$ for each message. Capacity uses all real $T\to\infty$ and $\lceil e^{TR}\rceil$ messages. At $E=0$ it is zero; at $E>0$ a $\theta>0$ satisfies
--
--   $$\frac1{2\pi}\int_{\omega_-}^{\omega_+}\hbar\omega\left(\frac1{e^{\theta\hbar\omega}-1}-N(\omega)\right)_+d\omega=E,$$
--
--   and
--
--   $$C=\frac1{2\pi}\int_{\omega_-}^{\omega_+}\left[g\left(\frac1{e^{\theta\hbar\omega}-1}\right)-g(N(\omega))\right]_+d\omega,
--   \qquad \lim_{T\to\infty}\frac{C_T}{T}=C.$$
--
--   Here $C_T$ is the total finite-mode Holevo optimum under energy $TE$. This is the periodic finite-mode model; it asserts no capacity result for the formal continuum CCR process.
-- source:
--   Coding Theorems for Quantum Channels, arXiv:quant-ph/9809023v1, PDF p. 32, Proposition 4: band-limited periodic waveform coding capacity

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

/-- Proposition 4, finite-band regime, PDF pp.31-34, (125)-(127).
Positive real observation times tend to infinity; an empty short-time mode set
is harmless. At zero power capacity is zero with no finite theta requirement. -/
theorem bandLimitedWaveform (hbar low high E : ℝ) (N : ℝ → ℝ)
    (hhbar : 0 < hbar) (hlow : 0 < low) (hband : low < high)
    (hE : 0 ≤ E) (hN : ∀ omega ∈ Set.Icc low high, 0 ≤ N omega)
    (hcontinuous : ContinuousOn N (Set.Icc low high)) :
    (E = 0 → waveformCapacity hbar N (fun _ => low) (fun _ => high) E = 0) ∧
    (0 < E → ∃ theta : ℝ, 0 < theta ∧
      (∫ omega in low..high, hbar * omega * spectralAllocation hbar theta N omega) /
        (2 * Real.pi) = E ∧
      let C := (∫ omega in low..high,
        max (g (planck hbar theta omega) - g (N omega)) 0) / (2 * Real.pi)
      waveformCapacity hbar N (fun _ => low) (fun _ => high) E = ENNReal.ofReal C ∧
      Tendsto (fun T : ℝ => waveformInformation hbar N low high E T / T)
        atTop (nhds C)) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P44

end
