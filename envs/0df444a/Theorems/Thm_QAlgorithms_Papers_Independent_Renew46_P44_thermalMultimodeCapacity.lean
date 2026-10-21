-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P44_thermalMultimodeCapacity
-- name    : QAlgorithms.Papers.Independent.Renew46.P44.thermalMultimodeCapacity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T21:43:17.901365+00:00
-- url     : https://prove2.me/theorems/741ce6d2-f05b-4a60-a85b-ebaf865e4dfa
-- title:
--   §V.3, (115)–(116): equilibrium and pure multimode capacities
-- statement:
--   For a finite collection of modes with $\hbar>0$ and $\omega_j>0$, define $s(P)$ as the maximum $\sum_jg(m_j)$ over $m_j\ge0$ with $\sum_j\hbar\omega_jm_j\le P$. For equilibrium noise $N_j=(e^{\theta_P\hbar\omega_j}-1)^{-1}$, where $\theta_P>0$ and $P=\sum_j\hbar\omega_jN_j$, one has $s(P)=\sum_jg(N_j)$ and, for signal budget $E\ge0$,
--
--   $$C=s(P+E)-s(P).$$
--
--   For the separate pure channel $N_j=0$,
--
--   $$C=s(E).$$
--
--   These are operational capacities of product displaced thermal alphabets with a common collective receiver. The pure $P=0$ endpoint is not represented by a nonexistent finite-temperature parameter.
-- source:
--   Coding Theorems for Quantum Channels, arXiv:quant-ph/9809023v1, PDF p. 30, §V.3, (115)–(116): equilibrium and pure multimode capacities

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

/-- Equations (115)-(116), PDF p.30: equilibrium and pure channels have their
own explicit entropy-difference capacities. Theta_P>0 describes P>0 noise;
the pure P=0 channel is stated separately in the same conclusion. -/
theorem thermalMultimodeCapacity {J : Type} [Fintype J]
    (hbar thetaP E : ℝ) (omega : J → ℝ)
    (hhbar : 0 < hbar) (hthetaP : 0 < thetaP)
    (homega : ∀ j, 0 < omega j) (hE : 0 ≤ E) :
    let N := fun j => planck hbar thetaP (omega j)
    let P := ∑ j, hbar * omega j * N j
    thermalEntropyBudget hbar omega P = ∑ j, g (N j) ∧
    averageErrorCqCapacity (multimodeOutput N) (modeCost hbar omega) E =
      ENNReal.ofReal (thermalEntropyBudget hbar omega (P + E) -
        thermalEntropyBudget hbar omega P) ∧
    averageErrorCqCapacity (multimodeOutput (fun _ : J => 0)) (modeCost hbar omega) E =
      ENNReal.ofReal (thermalEntropyBudget hbar omega E) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P44

end
