-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P48_adc_choi
-- name    : QAlgorithms.Papers.Independent.Information100.P48.adc_choi
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T11:45:42.873827+00:00
-- url     : https://prove2.me/theorems/fa557107-c530-4221-a8f0-09a2bee533ff
-- title:
--   ADC Choi operator, spatial tensor and attained CHSH maximum
-- statement:
--   For $\gamma\in[0,1]$, apply the ADC to the output half of $|\Phi^+\rangle=(|00\rangle+|11\rangle)/\sqrt2$, with reference first. The normalized Choi state is
--
--   $$
--   J_\gamma=\frac12\begin{pmatrix}1&0&0&\sqrt{1-\gamma}\\0&0&0&0\\0&0&\gamma&0\\\sqrt{1-\gamma}&0&0&1-\gamma\end{pmatrix},
--   \quad T=\operatorname{diag}(\sqrt{1-\gamma},-\sqrt{1-\gamma},1-\gamma).
--   $$
--
--   Here $T_{ij}=\operatorname{Tr}[J_\gamma(\sigma_i\otimes\sigma_j)]$ in $X,Y,Z$ order. Over arbitrary four unit Bloch directions, the spatial CHSH maximum is attained and equals $2\sqrt{2(1-\gamma)}$, which exceeds two exactly for $\gamma<1/2$. For any two unit Bloch observables $A,B$, the temporal correlation from input $I/2$ equals $\operatorname{Tr}[J_\gamma(A^T\otimes B)]$. This states both the concrete ADC calculation and its required Alice-transpose convention.
-- source:
--   Coherent Control of Channel Dilations Activate Temporal Bell Nonclassicality, arXiv:2607.05643v1, PDF p. 11, Appendix A, Eqs.(A4)–(A8): ADC Choi matrix, tensor and CHSH

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P48

namespace QAlgorithms.Papers.Independent.Information100.P48

open scoped Matrix ComplexConjugate

noncomputable section

/-- Appendix A, PDF p.11, Eqs.(A4)–(A8): ADC Choi matrix, tensor and attained
spatial CHSH maximum. The temporal correspondence transposes Alice's observable. -/
theorem adc_choi (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) :
    choi (adc g) = adcChoiMatrix g ∧
    IsDensityMatrix (choi (adc g)) ∧
    correlationTensor (choi (adc g)) =
      Matrix.diagonal ![Real.sqrt (1 - g), -Real.sqrt (1 - g), 1 - g] ∧
    IsGreatest (spatialValues (choi (adc g))) (2 * Real.sqrt (2 * (1 - g))) ∧
    (2 < 2 * Real.sqrt (2 * (1 - g)) ↔ g < 1 / 2) ∧
    (∀ a b : Fin 3 → ℝ, UnitDirection a → UnitDirection b →
      correlator (adc g) (bloch a) (bloch b) =
        (choi (adc g) * Matrix.kronecker (bloch a).transpose (bloch b)).trace.re) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P48
