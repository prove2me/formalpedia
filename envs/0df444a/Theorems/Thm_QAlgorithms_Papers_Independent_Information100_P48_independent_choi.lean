-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P48_independent_choi
-- name    : QAlgorithms.Papers.Independent.Information100.P48.independent_choi
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T11:46:26.404132+00:00
-- url     : https://prove2.me/theorems/71233a92-bcc2-43bb-9662-d16cdd628e33
-- title:
--   Independent-control Choi state and corrected unrestricted spatial maximum
-- statement:
--   Let $\gamma\in[0,1]$ and use the independent-environment coherent ADC $+$ map. Its Bell-input Choi operator has trace $1-\gamma/4>0$. After normalization, in reference/output order,
--
--   $$
--   J^{\rm ind}_+=\frac1{4-\gamma}\begin{pmatrix}2&0&0&2\sqrt{1-\gamma}\\0&0&0&0\\0&0&\gamma&0\\2\sqrt{1-\gamma}&0&0&2(1-\gamma)\end{pmatrix}.
--   $$
--
--   This is a density matrix, with tensor $\operatorname{diag}(4\sqrt{1-\gamma}/(4-\gamma),-4\sqrt{1-\gamma}/(4-\gamma),(4-3\gamma)/(4-\gamma))$. Its unrestricted spatial CHSH maximum is attained and equals
--
--   $$
--   S_{\max}^{\rm ind}=\begin{cases}\dfrac{8\sqrt{2-2\gamma}}{4-\gamma},&\gamma\le8/9,\\[3pt]\dfrac{2\sqrt{16(1-\gamma)+(4-3\gamma)^2}}{4-\gamma},&\gamma>8/9.\end{cases}
--   $$
--
--   Strict violation is equivalent to $\gamma<4\sqrt{10}-12$. This corrects the source's global eigenvalue ordering while preserving its activation threshold.
-- source:
--   Coherent Control of Channel Dilations Activate Temporal Bell Nonclassicality, arXiv:2607.05643v1, PDF p. 12, Appendix A(a), Eqs.(A9)–(A12): independent-control Choi operator and corrected eigenvalue ordering

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P48

namespace QAlgorithms.Papers.Independent.Information100.P48

open scoped Matrix ComplexConjugate

noncomputable section

/-- Appendix A(a), PDF p.12, Eqs.(A9)–(A12), with explicit source corrections:
(A11)'s two equatorial eigenvalues are largest only up to gamma=8/9; thereafter
z enters the optimizing pair. The sentence after (A12) reverses the violation
direction: violation is below the crossing. At gamma=1 the maximum is 2/3, not 0.
The fixed-equatorial Eq.(53) remains valid throughout [0,1]. -/
theorem independent_choi (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) :
    (choi (independentADC g false)).trace.re = 1 - g / 4 ∧
    conditionalChoi (independentADC g false) = independentChoiMatrix g ∧
    IsDensityMatrix (conditionalChoi (independentADC g false)) ∧
    correlationTensor (conditionalChoi (independentADC g false)) =
      Matrix.diagonal ![4 * Real.sqrt (1 - g) / (4 - g),
        -4 * Real.sqrt (1 - g) / (4 - g), (4 - 3 * g) / (4 - g)] ∧
    IsGreatest (spatialValues (conditionalChoi (independentADC g false)))
      (independentSpatialMaximum g) ∧
    (2 < independentSpatialMaximum g ↔ g < independentCritical) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P48
