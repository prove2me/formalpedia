-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P16_vacuumTransforms
-- name    : QAlgorithms.Papers.Independent.Next46.P16.vacuumTransforms
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T15:11:14.787616+00:00
-- url     : https://prove2.me/theorems/9a84af02-464c-4153-9edb-0b636cd767e0
-- title:
--   The vacuum kernel, characteristic function and Wigner function
-- statement:
--   Fix $N\ge1$ and write $|q|^2=\sum_{j=1}^Nq_j^2$. Let $h_0(q)=\pi^{-N/4}e^{-|q|^2/2}$ be the normalized oscillator ground-state wavefunction and $T_0=|h_0\rangle\langle h_0|$. With $\chi_{T_0}(q,p)=\operatorname{Tr}(W(q,p)T_0)$ and phase measure $dx=(2\pi)^{-N}dq\,dp$, the three functions are
--   $$
--   K_{T_0}(q,q')=\pi^{-N/2}e^{-(|q|^2+|q'|^2)/2},\qquad
--   \chi_{T_0}(q,p)=e^{-(|q|^2+|p|^2)/4},\qquad
--   w_{T_0}(q,p)=2^N e^{-(|q|^2+|p|^2)}.
--   $$
--   The characteristic and Wigner functions are defined by their concrete rank-one integrals from (2), (4) and p.21, with complex conjugation on the bra wavefunction. This benchmark distinguishes the kernel, characteristic and Wigner normalizations.
-- source:
--   Schwartz operators, arXiv:1503.04086v1, PDF p. 22, VacuumTransforms

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P16

noncomputable section

open MeasureTheory Filter

open QAlgorithms.Papers.Independent.Claimed50.P10 (Configuration)

open QAlgorithms.Papers.Independent.Dependency50.P13 (IsTraceClass)

open scoped BigOperators ENNReal ComplexOrder

namespace QAlgorithms.Papers.Independent.Next46.P16

attribute [local instance] QAlgorithms.Papers.Independent.Next46.P16.canonicalComplexCalculus

attribute [local instance] QAlgorithms.Papers.Independent.Next46.P16.canonicalRealCalculus

attribute [local instance] QAlgorithms.Papers.Independent.Next46.P16.canonicalRealNonUnitalCalculus

/-- Gaussian normalization benchmark, PDF p.22, with definitions (2),(4) on
p.3 and the rank-one Wigner formula on p.21. These are three different functions:
the kernel, characteristic function, and source-normalized Wigner function. -/
theorem vacuumTransforms (n : ℕ) (hn : 0 < n) :
    (∀ q qr : Configuration n,
      rankOneKernel (vacuumWave n) (vacuumWave n) q qr =
        ((Real.rpow Real.pi (-(n : ℝ) / 2) *
          Real.exp (-((∑ i, q i ^ 2) + (∑ i, qr i ^ 2)) / 2) : ℝ) : ℂ)) ∧
    (∀ q p : Configuration n,
      rankOneCharacteristic (vacuumWave n) (vacuumWave n) q p =
        ((Real.exp (-((∑ i, q i ^ 2) + (∑ i, p i ^ 2)) / 4) : ℝ) : ℂ)) ∧
    (∀ q p : Configuration n,
      rankOneWigner (vacuumWave n) (vacuumWave n) q p =
        (((2 : ℝ) ^ n * Real.exp (-((∑ i, q i ^ 2) + (∑ i, p i ^ 2))) : ℝ) : ℂ)) := by sorry

end QAlgorithms.Papers.Independent.Next46.P16

end
