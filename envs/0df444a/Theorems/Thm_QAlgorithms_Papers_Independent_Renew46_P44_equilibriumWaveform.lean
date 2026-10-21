-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P44_equilibriumWaveform
-- name    : QAlgorithms.Papers.Independent.Renew46.P44.equilibriumWaveform
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T21:45:20.635733+00:00
-- url     : https://prove2.me/theorems/2a5e22b8-cd6b-4198-867b-03122d3a4b26
-- title:
--   §V.4, (145)–(147): equilibrium and noiseless infinite-band capacities
-- statement:
--   Fix $\hbar>0$ and finite powers $P,E\ge0$ in the periodic finite-mode infinite-band limit, with positive cutoffs decreasing to zero and increasing to infinity. For $P>0$ put $\theta_P=\sqrt{\pi/(12\hbar P)}$ and $N_P(\omega)=(e^{\theta_P\hbar\omega}-1)^{-1}$; at $P=0$ put $N_P=0$. Then
--
--   $$\frac1{2\pi}\int_0^\infty\hbar\omega N_P(\omega)d\omega=P,\qquad
--   s(P)=\frac1{2\pi}\int_0^\infty g(N_P(\omega))d\omega=\sqrt{\frac{\pi P}{3\hbar}},$$
--
--   $$C=\sqrt{\frac{\pi(P+E)}{3\hbar}}-\sqrt{\frac{\pi P}{3\hbar}}.$$
--
--   In particular the pure channel has capacity $\sqrt{\pi E/(3\hbar)}$. The quantities are in nats per unit observation time and retain the frequency-density factor $1/(2\pi)$.
-- source:
--   Coding Theorems for Quantum Channels, arXiv:quant-ph/9809023v1, PDF p. 36, §V.4, (145)–(147): equilibrium and noiseless infinite-band capacities

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

/-- Equations (145)-(147), PDF pp.36-37. The 1/(2pi) frequency density and
hbar are retained, including equilibrium and vacuum endpoints. -/
theorem equilibriumWaveform (hbar P E : ℝ) (windows : FrequencyWindows)
    (hhbar : 0 < hbar) (hP : 0 ≤ P) (hE : 0 ≤ E) :
    (∫ omega in Set.Ioi (0 : ℝ), hbar * omega * equilibriumNoise hbar P omega) /
      (2 * Real.pi) = P ∧
    (∫ omega in Set.Ioi (0 : ℝ), g (equilibriumNoise hbar P omega)) /
      (2 * Real.pi) = Real.sqrt (Real.pi * P / (3 * hbar)) ∧
    waveformCapacity hbar (equilibriumNoise hbar P) windows.low windows.high E =
      ENNReal.ofReal (Real.sqrt (Real.pi * (P + E) / (3 * hbar)) -
        Real.sqrt (Real.pi * P / (3 * hbar))) ∧
    waveformCapacity hbar (fun _ => 0) windows.low windows.high E =
      ENNReal.ofReal (Real.sqrt (Real.pi * E / (3 * hbar))) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P44

end
