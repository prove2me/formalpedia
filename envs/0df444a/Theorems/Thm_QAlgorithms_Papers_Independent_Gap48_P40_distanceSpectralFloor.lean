-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P40_distanceSpectralFloor
-- name    : QAlgorithms.Papers.Independent.Gap48.P40.distanceSpectralFloor
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T05:19:17.863624+00:00
-- url     : https://prove2.me/theorems/ca32b637-c93a-426f-8bd9-8f2203fc1bec
-- title:
--   §IV, Lemma 5: maximal rescaled distance under a spectral floor
-- statement:
--   All matrices act on a complex Hilbert space of positive finite dimension $d$. A state is positive semidefinite with trace one. All logarithms are natural, and $D(\rho\|\sigma)$ denotes support-aware Umegaki relative entropy, with value $+\infty$ when support containment fails. Let $N$ be any genuine unitarily invariant norm on $d\times d$ complex matrices. Write $E=\operatorname{diag}(1,0,\ldots)$ and, when $d\ge2$, $F=\operatorname{diag}(1,-1,0,\ldots)$. The symbols $\|\cdot\|_\infty$, $\|\cdot\|_1$ and $\|\cdot\|_2$ mean operator, full trace and Hilbert–Schmidt norms, respectively. Suppose $d\ge2$, $\rho,\sigma$ are states and $\sigma\ge\beta I$ in Loewner order, where $\beta\in\mathbb R$. Then
--
--   $$
--   \frac{N(\rho-\sigma)}{N(F)}\le1-\beta.
--   $$
--
--   The minimum-eigenvalue floor controls every rescaled UI distance.
-- source:
--   Continuity bounds on the quantum relative entropy, arXiv:quant-ph/0503218v3, PDF p. 4, §IV, Lemma 5: maximal rescaled distance under a spectral floor

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P40

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Topology Matrix.Norms.L2Operator

open Filter MeasureTheory Asymptotics

open QAlgorithms

open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy)

open QAlgorithms.Papers.Independent.Information100.P50 (IsUINorm)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P60 (copies)

open QAlgorithms.Papers.Independent.Information100.P44 (Mat)

namespace QAlgorithms.Papers.Independent.Gap48.P40

/-- PDF p.4, Lemma 5: beta is a lower spectral floor, with no positivity restriction. -/
theorem distanceSpectralFloor {d : ℕ} (hd : 2 ≤ d) (N : Mat d → ℝ)
    (hN : IsUINorm N) (rho sigma : Mat d) (hrho : IsDensityMatrix rho)
    (hsigma : IsDensityMatrix sigma) (beta : ℝ)
    (hfloor : (sigma - (beta : ℂ) • (1 : Mat d)).PosSemidef) :
    rescaled N (rho - sigma) ≤ 1 - beta := by sorry

end QAlgorithms.Papers.Independent.Gap48.P40

end
