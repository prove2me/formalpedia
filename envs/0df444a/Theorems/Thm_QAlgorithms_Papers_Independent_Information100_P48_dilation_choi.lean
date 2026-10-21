-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P48_dilation_choi
-- name    : QAlgorithms.Papers.Independent.Information100.P48.dilation_choi
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T11:46:55.983282+00:00
-- url     : https://prove2.me/theorems/c65c3b7e-6a0f-4978-b356-688e4c4d5ace
-- title:
--   Shared-dilation Choi state and unrestricted spatial CHSH maximum
-- statement:
--   Let $\gamma\in[0,1]$ and use the shared-environment forward/inverse coherent ADC $+$ map. Its Bell-input Choi operator has trace $1-\gamma/2>0$. Its normalized density matrix is
--
--   $$
--   J^D_+=\frac1{2-\gamma}\begin{pmatrix}1&0&0&\sqrt{1-\gamma}\\0&0&0&0\\0&0&0&0\\\sqrt{1-\gamma}&0&0&1-\gamma\end{pmatrix},
--   $$
--
--   with spatial tensor $\operatorname{diag}(2\sqrt{1-\gamma}/(2-\gamma),-2\sqrt{1-\gamma}/(2-\gamma),1)$. The CHSH maximum over arbitrary four local unit Bloch directions is attained and is
--
--   $$
--   S^D_{\max}=2\sqrt{1+\frac{4(1-\gamma)}{(2-\gamma)^2}}>2\quad\Longleftrightarrow\quad\gamma<1.
--   $$
--
--   This unrestricted spatial maximum is distinct from the fixed-equatorial temporal value of Eq.(54); full damping is not a strict violation.
-- source:
--   Coherent Control of Channel Dilations Activate Temporal Bell Nonclassicality, arXiv:2607.05643v1, PDF p. 12, Appendix A(b), Eqs.(A13)–(A15): dilation-control Choi state and unrestricted CHSH

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P48

namespace QAlgorithms.Papers.Independent.Information100.P48

open scoped Matrix ComplexConjugate

noncomputable section

/-- Appendix A(b), PDF p.12, Eqs.(A13)–(A15): unrestricted spatial CHSH maximum
of the selected Choi state. The source's phrase entire range excludes gamma=1,
as its strict displayed inequality requires. This is not Eq.(54)'s fixed value. -/
theorem dilation_choi (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) :
    (choi (sharedADC g false)).trace.re = 1 - g / 2 ∧
    conditionalChoi (sharedADC g false) = sharedChoiMatrix g ∧
    IsDensityMatrix (conditionalChoi (sharedADC g false)) ∧
    correlationTensor (conditionalChoi (sharedADC g false)) =
      Matrix.diagonal ![2 * Real.sqrt (1 - g) / (2 - g),
        -2 * Real.sqrt (1 - g) / (2 - g), 1] ∧
    IsGreatest (spatialValues (conditionalChoi (sharedADC g false)))
      (2 * Real.sqrt (1 + 4 * (1 - g) / (2 - g) ^ 2)) ∧
    (2 < 2 * Real.sqrt (1 + 4 * (1 - g) / (2 - g) ^ 2) ↔ g < 1) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P48
