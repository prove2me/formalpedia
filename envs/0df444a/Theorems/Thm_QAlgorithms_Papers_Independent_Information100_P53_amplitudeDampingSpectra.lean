-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P53_amplitudeDampingSpectra
-- name    : QAlgorithms.Papers.Independent.Information100.P53.amplitudeDampingSpectra
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T11:54:23.610867+00:00
-- url     : https://prove2.me/theorems/6b966d90-d789-4eae-9b93-0c7a84cb7c33
-- title:
--   Lemma-3
-- statement:
--   Let $a,\gamma\in[0,1]$, $f\in\mathbb R$, and $b=\sqrt{a(1-a)}$. Define
--   $$\rho_0=\begin{pmatrix}a&be^{if}\\be^{-if}&1-a\end{pmatrix},\qquad
--   \rho_1=I-\rho_0.$$
--   Let $\mathcal N_\gamma(A)=K_0AK_0^\dagger+K_1AK_1^\dagger$, where $K_0=\operatorname{diag}(1,\sqrt{1-\gamma})$ and $K_1=\begin{pmatrix}0&\sqrt\gamma\\0&0\end{pmatrix}$. With $c_a=\gamma(1-\gamma)(1-a)^2$, the complete decreasing output spectra are
--   $$\operatorname{spec}(\mathcal N_\gamma(\rho_0))=\left(\frac{1+\sqrt{1-4c_a}}2,\frac{1-\sqrt{1-4c_a}}2\right),$$
--   $$\operatorname{spec}(\mathcal N_\gamma(\rho_1))=\left(\frac{1+\sqrt{1-4c_{1-a}}}2,\frac{1-\sqrt{1-4c_{1-a}}}2\right).$$
--
--   These formulas identify the single-use spectra needed for product-state amplitude-damping converses.
-- source:
--   A Spectrum-Based Converse for Quantum State Discrimination and Its Applications to Classical-Quantum Channel Coding, arXiv:2610.06840v1, PDF p. 3, Lemma-3

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P53

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P53

open scoped Matrix ComplexConjugate ComplexOrder

open Finset

/-- PDF p.3, Lemma 3: both descending output spectra for the two specified inputs.
The complementary input is I−rho0; a and gamma range over [0,1]. -/
theorem amplitudeDampingSpectra (a f gamma : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hg : 0 ≤ gamma) (hg1 : gamma ≤ 1) :
    ∃ (s0 : SpectralData (amplitudeDamping gamma (qubitInput a f)))
      (s1 : SpectralData (amplitudeDamping gamma (1 - qubitInput a f))),
      s0.value = ![(1 + Real.sqrt (1 - 4 * gamma * (1 - gamma) * (1 - a) ^ 2)) / 2,
        (1 - Real.sqrt (1 - 4 * gamma * (1 - gamma) * (1 - a) ^ 2)) / 2] ∧
      s1.value = ![(1 + Real.sqrt (1 - 4 * gamma * (1 - gamma) * a ^ 2)) / 2,
        (1 - Real.sqrt (1 - 4 * gamma * (1 - gamma) * a ^ 2)) / 2] := by sorry

end QAlgorithms.Papers.Independent.Information100.P53

end
