-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P38_channel_fidelity
-- name    : QAlgorithms.Papers.Independent.Extend50.P38.channel_fidelity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:49:31.007003+00:00
-- url     : https://prove2.me/theorems/700ce54c-a8b0-42c4-b025-c4bbca413ffa
-- title:
--   Physical port-selection channel and its fidelity objective
-- statement:
--   Let $d,N\geq1$. Alice and Bob share the pure resource $|\psi_O\rangle=(O_A\otimes I_B)|\phi_d^+\rangle^{\otimes N}$, where $\operatorname{Tr}(OO^\dagger)=d^N$ and $|\phi_d^+\rangle=d^{-1/2}\sum_{k=0}^{d-1}|kk\rangle$. Alice uses an $N$-outcome POVM $\{\Pi_i\}$ on her $N$ ports and the input; Bob retains only $B_i$, relabelled $B$, without a correction. This defines a CPTP map $\Lambda$, and the resource density is normalized. Set $\sigma_i=d^{-(N-1)}P^+_{A_iB}\otimes I_{\bar A_i}$. Its entanglement fidelity and Haar-average pure-input fidelity satisfy
--
--   $$F=\operatorname{Tr}\!\left[P^+_{BD}(\Lambda\otimes\operatorname{id}_D)(P^+_{CD})\right]=\frac1{d^2}\sum_{i=1}^N\operatorname{Tr}\!\left[\Pi_i(O\otimes I)\sigma_i(O^\dagger\otimes I)\right],\qquad f=\frac{dF+1}{d+1}.$$
--
--   This identifies the operational teleportation channel with the optimization objective used in the paper.
-- source:
--   Asymptotic teleportation scheme as a universal programmable quantum processor, arXiv:0807.4568v2, PDF p. 2, Eq. (2) and preceding physical channel display

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P38

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P38

attribute [local instance] Classical.propDecidable Classical.decEq

-- Pinned accepted definitions; neither is re-declared in this module.

open QAlgorithms.Papers.Independent.Frontier18.P14 (singlet)

open QAlgorithms.Papers.Independent.Renew46.P01 (SpinPath)

/-- PDF p.2, physical channel display, Eq.(2), and its Haar-average specialization.
The normalization and POVM hypotheses are the section's actual standing assumptions. -/
theorem channel_fidelity (d N : ℕ) (hd : 0 < d) (hN : 0 < N)
    (O : Matrix (Ports d N) (Ports d N) ℂ) (hO : ValidResource O)
    (M : Fin N → Matrix (AC d N) (AC d N) ℂ) (hM : IsPOVM M) :
    IsDensityMatrix (resourceDensity O) ∧ IsChannel (teleport O M) ∧
    QuditFidelity.entanglementFidelity d hd (teleport O M) = teleportationObjective O M ∧
    QuditFidelity.averageFidelity d hd (teleport O M) =
      ((d : ℝ) * QuditFidelity.entanglementFidelity d hd (teleport O M) + 1) /
        ((d : ℝ) + 1) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P38

end
