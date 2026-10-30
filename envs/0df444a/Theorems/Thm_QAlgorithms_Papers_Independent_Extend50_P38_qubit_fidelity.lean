-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P38_qubit_fidelity
-- name    : QAlgorithms.Papers.Independent.Extend50.P38.qubit_fidelity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:52:00.895007+00:00
-- url     : https://prove2.me/theorems/2ccd5639-c7fc-457e-b2c4-3755dcbf01be
-- title:
--   Exact qubit SRM entanglement fidelity
-- statement:
--   For $N\geq1$, use $N$ spin singlets as the resource and let Alice perform the square-root measurement of the singlet signals, completed by $\Delta=(I-\sum_i\rho^{-1/2}\sigma_i\rho^{-1/2})/N$ on every outcome. These effects form a POVM and the resulting port-selection map $\Lambda_N$ is a channel. Its entanglement fidelity is
--
--   $$F_N=\frac1{2^{N+3}}\sum_{k=0}^N\binom Nk\left[\frac{N-2k-1}{\sqrt{k+1}}+\frac{N-2k+1}{\sqrt{N-k+1}}\right]^2,$$
--
--   and its Haar-average pure-input fidelity is $f_N=(2F_N+1)/3$. This is an identity for the physical protocol, not a definition of its fidelity.
-- source:
--   Asymptotic teleportation scheme as a universal programmable quantum processor, arXiv:0807.4568v2, PDF p. 3, Last unnumbered display in right column

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P38

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P38

attribute [local instance] Classical.propDecidable Classical.decEq

-- Pinned accepted definitions; neither is re-declared in this module.

open QAlgorithms.Papers.Independent.Frontier18.P14 (singlet)

open QAlgorithms.Papers.Independent.Renew46.P01 (SpinPath)

/-- PDF p.3, last unnumbered fidelity display: exact entanglement fidelity of the
physical singlet-resource SRM channel, with its normalized kernel completion. -/
theorem qubit_fidelity (N : ℕ) (hN : 0 < N) :
    IsPOVM (srm (singletSignals N)) ∧ IsChannel (singletSrmChannel N) ∧
    QuditFidelity.entanglementFidelity 2 (by decide) (singletSrmChannel N) = qubitClosedF N ∧
    qubitAverage N = (2 * qubitClosedF N + 1) / 3 := by sorry

end QAlgorithms.Papers.Independent.Extend50.P38

end
