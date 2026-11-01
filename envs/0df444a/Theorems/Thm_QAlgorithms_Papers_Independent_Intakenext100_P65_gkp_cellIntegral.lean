-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P65_gkp_cellIntegral
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P65.gkp_cellIntegral
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:36:47.311218+00:00
-- url     : https://prove2.me/theorems/51d90e7a-cd75-4ca8-a0c0-9b775bdb0776
-- title:
--   Central square-cell probability and strict Gaussian tail bound
-- statement:
--   Let $0<\gamma<1$ and $p_\gamma(\alpha)=(1-\gamma)(\pi\gamma)^{-1}e^{-(1-\gamma)|\alpha|^2/\gamma}$. This density defines a probability measure on the complex plane. Put $b=\sqrt{\pi/8}$ and $Q=\{\alpha:|\Re\alpha|,|\Im\alpha|\le b\}$. The central-cell success and failure probabilities obey
--
--   $$P_{\rm succ}=\int_Qp_\gamma(\alpha)\,d^2\alpha,\qquad P_{\rm fail}=1-P_{\rm succ}<\int_{|\alpha|\ge b}p_\gamma(\alpha)\,d^2\alpha=e^{-\pi(1-\gamma)/(8\gamma)}.$$
--
--   The strict inequality follows from the nonzero area between the inscribed disk and the square. Identity-coset translates can also be corrected, so $P_{\rm fail}$ is an upper bound on logical infidelity, not its exact value.
-- source:
--   Performance and structure of single-mode bosonic codes, arXiv:1708.05010v3, PDF p. 20, §VII B (7.23)–(7.24): correctable-cell probability and Gaussian tail

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P65

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P65

open MeasureTheory Filter

open QAlgorithms.Papers.Independent.Frontier18.P14 (displacementEntry)

open QAlgorithms.Papers.Independent.Dependency50.P40 (outputFirstChoi)

open scoped ComplexConjugate Matrix Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- PDF pp.20--21 (7.23)--(7.24): central-cell integral and strict circular-tail
bound; this failure probability is not identified with the exact logical infidelity. -/
theorem gkp_cellIntegral (g : ℝ) (hg0 : 0 < g) (hg1 : g < 1) :
    (amplifiedLossLaw g Set.univ = 1) ∧
    centralSuccess g =
      (∫ z in {z : ℂ | |z.re| ≤ Real.sqrt (Real.pi / 8) ∧ |z.im| ≤ Real.sqrt (Real.pi / 8)},
        amplifiedLossDensity g z) ∧
    centralFailure g = 1 - centralSuccess g ∧
    centralFailure g <
      (∫ z in {z : ℂ | Real.sqrt (Real.pi / 8) ≤ ‖z‖}, amplifiedLossDensity g z) ∧
    (∫ z in {z : ℂ | Real.sqrt (Real.pi / 8) ≤ ‖z‖}, amplifiedLossDensity g z) =
      Real.exp (-Real.pi * (1 - g) / (8 * g)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P65

end
