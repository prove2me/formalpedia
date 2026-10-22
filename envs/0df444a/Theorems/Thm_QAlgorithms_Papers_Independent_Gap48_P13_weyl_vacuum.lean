-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P13_weyl_vacuum
-- name    : QAlgorithms.Papers.Independent.Gap48.P13.weyl_vacuum
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T21:39:31.287355+00:00
-- url     : https://prove2.me/theorems/8e6fe6d0-d9a7-403c-8ab0-56162a6410d1
-- title:
--   Corrected action of the Weyl unitary on vacuum
-- statement:
--   For $z\in\mathbb C$, let $W(z)=\exp(za-\overline z a^+)$, let $\phi_0$ be the norm-one oscillator vacuum, and let $e(u)=\sum_{n\ge0}u^n\phi_n/\sqrt{n!}$. Then
--
--   $$W(z)\phi_0=e^{-|z|^2/2}\exp(-\overline z a^+)\phi_0=\frac{e(-\overline z)}{\|e(-\overline z)\|}.$$
--
--   The creation exponential means its convergent vacuum vector series. The result identifies the normalized coherent vector produced by the source's Weyl convention.
--
--   **Formalization Note** The printed middle and final expressions use $z$ in place of $-\overline z$. The correction follows the source's own definitions (7) and (12); its printed statement is preserved in the verbatim field and requires independent moderation.
-- source:
--   Markov triplets on CCR-algebras, arXiv:0812.3724v2, PDF p. 5, Lemma 1.2

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P13

noncomputable section

open Filter MeasureTheory

open scoped BigOperators Topology ENNReal ComplexOrder Matrix Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace QAlgorithms.Papers.Independent.Gap48.P13

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Dependency50.P21 (imaginaryPower)

/-- Lemma 1.2, PDF p.5, corrected against (7),(12): the printed exp(z a+) and e(z)
are replaced by exp(-conj(z) a+) and e(-conj(z)). For real z the first excited
coefficient is -z exp(-z^2/2), which disproves the printed sign. -/
theorem weyl_vacuum (z : ℂ) :
    (Osc.HasFockMatrix (Osc.displacement (-star z)) (Osc.displacementMatrix (-star z)) ∧
      (ContinuousLinearMap.adjoint (Osc.displacement (-star z))).comp (Osc.displacement (-star z)) = 1 ∧
      (Osc.displacement (-star z)).comp (ContinuousLinearMap.adjoint (Osc.displacement (-star z))) = 1) ∧
    (Osc.displacement (-star z)) (Osc.fockKet 0) =
      (Real.exp (-Complex.normSq z / 2) : ℂ) •
        creationExponentialVacuum (-star z) ∧
    (Osc.displacement (-star z)) (Osc.fockKet 0) =
      ((‖exponentialVector (-star z)‖)⁻¹ : ℂ) • exponentialVector (-star z) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P13

end
