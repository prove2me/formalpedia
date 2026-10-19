-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P14_amplifierParametrization
-- name    : QAlgorithms.Papers.Independent.Frontier18.P14.amplifierParametrization
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:07:17.622208+00:00
-- url     : https://prove2.me/theorems/ac4fe38f-bee4-4f5d-9cf9-395122a6e7f5
-- title:
--   Complete canonical amplifier parametrization
-- statement:
--   For a two-mode amplifier acting on $(a_1,a_2^\dagger)$, write $J=\operatorname{diag}(1,-1)$. The condition $BJB^\dagger=J$ is equivalent to
--
--   $$|B_{11}|^2-|B_{12}|^2=1,\quad |B_{22}|^2-|B_{21}|^2=1,\quad \overline{B_{11}}B_{21}-\overline{B_{12}}B_{22}=0.$$
--
--   Every such $B$, and only such $B$, has real parameters $\Phi,\Theta,\Psi,\Lambda$ with
--
--   $$B=e^{i\Lambda/2}\operatorname{diag}(e^{i\Psi/2},e^{-i\Psi/2})\begin{pmatrix}\cosh(\Theta/2)&\sinh(\Theta/2)\\\sinh(\Theta/2)&\cosh(\Theta/2)\end{pmatrix}\operatorname{diag}(e^{i\Phi/2},e^{-i\Phi/2}).$$
--
--   The product equals the entries displayed in (6.4). The second equation corrects the printed sign error in (6.3), which fails at the identity. This classifies canonical pure amplification without scattering.
-- source:
--   Quantum Physics of Simple Optical Instruments, arXiv:quant-ph/0305007v2, PDF p. 29, §6.1: canonical amplifier matrices and their complete parametrization

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P14

noncomputable section

open scoped Matrix ComplexConjugate

open Filter

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Frontier18.P14

open QAlgorithms.Papers.Independent.Dependency50.P34 (fockKet)

/-- PDF pp.28–29, (6.2)–(6.5): complete canonical amplifier
parametrization. Correction to printed (6.3): the second equation is
|B22|²-|B21|²=1. The printed reverse order fails already at B=I; the
metric relation and (6.4) fix the correction unambiguously. -/
theorem amplifierParametrization :
    (∀ B : Matrix (Fin 2) (Fin 2) ℂ,
      (B * pairMetric * B.conjTranspose = pairMetric ↔
        Complex.normSq (B 0 0) - Complex.normSq (B 0 1) = 1 ∧
        Complex.normSq (B 1 1) - Complex.normSq (B 1 0) = 1 ∧
        star (B 0 0) * B 1 0 - star (B 0 1) * B 1 1 = 0)) ∧
    (∀ B : Matrix (Fin 2) (Fin 2) ℂ,
      B * pairMetric * B.conjTranspose = pairMetric ↔
        ∃ phi theta psi lam : ℝ, B = amplifierEuler phi theta psi lam) ∧
    (∀ phi theta psi lam : ℝ,
      amplifierEuler phi theta psi lam = Complex.exp (Complex.I * (lam / 2 : ℝ)) •
        (relativeModePhase psi * boost (theta / 2) * relativeModePhase phi)) := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P14

end
