-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P23_extremal_matrix_units
-- name    : QAlgorithms.Papers.Independent.Gap48.P23.extremal_matrix_units
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T23:07:02.106674+00:00
-- url     : https://prove2.me/theorems/992a4c24-be4a-41ce-8a9e-2ea3814c91b8
-- title:
--   Lemma E.3.
-- statement:
--   For $\ell\ge1$, input covariance is with $T^\ell(U)$ and output covariance with $U$, for every $U\in U(2)$. The channel $\Phi_{\rm Tr}^\ell$ embeds through $V^\ell$ and keeps the first qubit; $\Phi_{\rm UNOT}^\ell$ measures the normalized coherent-state POVM and prepares the orthogonal state. Let $D_\ell$ be the explicit real dual Clebsch–Gordan matrix (C.49),(C.54). The unnormalized Choi order is output tensor input.
--
--   For $\ell\ge1$, the exact action of both endpoints on every matrix unit $|w\rangle\langle v|$ is the piecewise formula (E.17)–(E.18). On diagonal units the populations are
--   $$\Phi_1^\ell(|w\rangle\langle w|)=\operatorname{diag}((\ell-w)/\ell,w/\ell),\quad\Phi_2^\ell(|w\rangle\langle w|)=\operatorname{diag}((w+1)/(\ell+2),(\ell+1-w)/(\ell+2)).$$
--   For $v=w+1$, the coefficients of $|0\rangle\langle1|$ are $\sqrt{(\ell-w)v}/\ell$ and $-\sqrt{(\ell+1-v)(w+1)}/(\ell+2)$; the reverse-neighbor coefficients are their corresponding transposes. Every other off-diagonal unit maps to zero.
--
--   This characterizes the physical postprocessing maps used in the template algorithm.
-- source:
--   Quantum majority vote, arXiv:2211.11729v1, PDF p. 74, Lemma E.3.

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P23

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P23

open MeasureTheory

open scoped ComplexConjugate Matrix ComplexOrder

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

-- Exact frozen coordinate helpers; no paper-local redeclarations.

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

/-- PDF pp.74-75, Lemma E.3: every matrix unit, including negative off-diagonal amplitudes. -/
theorem extremal_matrix_units (ell : ℕ) (hell : 1 ≤ ell) (w v : Fin (ell+1)) :
    extremalChannel ell false (Matrix.single w v 1) = traceMatrixUnit ell w v ∧
    extremalChannel ell true (Matrix.single w v 1) = notMatrixUnit ell w v := by sorry

end QAlgorithms.Papers.Independent.Gap48.P23

end
