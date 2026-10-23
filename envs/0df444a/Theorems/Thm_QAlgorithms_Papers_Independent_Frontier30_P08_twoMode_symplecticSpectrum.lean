-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P08_twoMode_symplecticSpectrum
-- name    : QAlgorithms.Papers.Independent.Frontier30.P08.twoMode_symplecticSpectrum
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T09:15:13.195716+00:00
-- url     : https://prove2.me/theorems/b404a2b7-e79a-4ea9-8fa2-673f503e4dfa
-- title:
--   Two-mode symplectic eigenvalues
-- statement:
--   Let $V=\begin{pmatrix}A&C\\C^T&B\end{pmatrix}$ be a real symmetric positive definite $4\times4$ matrix, with $2\times2$ blocks in the order $(q_1,p_1,q_2,p_2)$. Put $\Delta=\det A+\det B+2\det C$. Its ordered positive symplectic eigenvalues are
--
--   $$\nu_\pm=\sqrt{\frac{\Delta\pm\sqrt{\Delta^2-4\det V}}{2}},\qquad 0<\nu_-\le\nu_+.$$
--
--   Both radicands are valid: $\Delta^2-4\det V\ge0$ and $\Delta-\sqrt{\Delta^2-4\det V}>0$. There exists a real $S$ with $S\Omega S^T=\Omega$ and $V=S[(\nu_- I_2)\oplus(\nu_+ I_2)]S^T$. This supplies the actual Williamson form, including coincident eigenvalues, without imposing the stronger quantum uncertainty condition.
-- source:
--   Gaussian Quantum Information, arXiv:1110.3234v1, PDF p. 10, §II.C.3 Eq.(54): two-mode symplectic eigenvalues

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P08

noncomputable section

namespace QAlgorithms.Papers.Independent.Frontier30.P08

open scoped BigOperators ComplexOrder ENNReal

open QAlgorithms.Papers.Independent.Dependency50.P39 (Fock coherentCoefficient)

/-- PDF p.10, Eqs.(53)–(54): ordered symplectic eigenvalues and their actual
Williamson congruence, for every symmetric positive definite two-mode matrix. -/
theorem twoMode_symplecticSpectrum
    (V : Matrix (QuadratureIndex 2) (QuadratureIndex 2) ℝ) (hV : V.PosDef) :
    0 ≤ (twoModeDelta V) ^ 2 - 4 * V.det ∧
    0 < twoModeDelta V - Real.sqrt ((twoModeDelta V) ^ 2 - 4 * V.det) ∧
    (∀ k, 0 < twoModeSpectrum V k) ∧
    twoModeSpectrum V 0 ≤ twoModeSpectrum V 1 ∧
    ∃ S : Matrix (QuadratureIndex 2) (QuadratureIndex 2) ℝ,
      isSymplectic S ∧
      V = S * williamsonDiagonal (twoModeSpectrum V) * S.transpose := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P08

end
