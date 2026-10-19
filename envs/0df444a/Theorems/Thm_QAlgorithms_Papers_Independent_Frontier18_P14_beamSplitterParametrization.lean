-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P14_beamSplitterParametrization
-- name    : QAlgorithms.Papers.Independent.Frontier18.P14.beamSplitterParametrization
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:03:19.870921+00:00
-- url     : https://prove2.me/theorems/7fdf3a94-0908-46d7-a397-279f10759a84
-- title:
--   Complete lossless beam-splitter parametrization
-- statement:
--   Every unitary two-mode beam matrix $B$ admits real parameters $\Phi,\Theta,\Psi,\Lambda$ such that
--
--   $$B=e^{i\Lambda/2}\begin{pmatrix}e^{i\Psi/2}&0\\0&e^{-i\Psi/2}\end{pmatrix}\begin{pmatrix}\cos(\Theta/2)&\sin(\Theta/2)\\-\sin(\Theta/2)&\cos(\Theta/2)\end{pmatrix}\begin{pmatrix}e^{i\Phi/2}&0\\0&e^{-i\Phi/2}\end{pmatrix}.$$
--
--   Conversely every such matrix is unitary. The statement also identifies this product entry by entry with (4.3). This is a complete parametrization of lossless two-mode scattering, including the overall phase.
-- source:
--   Quantum Physics of Simple Optical Instruments, arXiv:quant-ph/0305007v2, PDF p. 17, §4.1: parametrization and factorization of every lossless beam splitter

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P14

noncomputable section

open scoped Matrix ComplexConjugate

open Filter

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Frontier18.P14

open QAlgorithms.Papers.Independent.Dependency50.P34 (fockKet)

/-- PDF pp.15,17, (4.2)–(4.4): all U(2) beam splitters, including
surjectivity of the parametrization and its exact ordered factorization. -/
theorem beamSplitterParametrization :
    (∀ B : Matrix (Fin 2) (Fin 2) ℂ,
      B ∈ Matrix.unitaryGroup (Fin 2) ℂ ↔
        ∃ phi theta psi lam : ℝ, B = beamEuler phi theta psi lam) ∧
    (∀ phi theta psi lam : ℝ,
      beamEuler phi theta psi lam = Complex.exp (Complex.I * (lam / 2 : ℝ)) •
        (relativeModePhase psi * realModeRotation (theta / 2) * relativeModePhase phi)) := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P14

end
