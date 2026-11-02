-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P62_isotropic_threshold
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P62.isotropic_threshold
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:31:48.486325+00:00
-- url     : https://prove2.me/theorems/ff0dd471-3321-49a3-b21c-9362b1281107
-- title:
--   Exact projective steering threshold of isotropic states
-- statement:
--   Let $d\ge2$ be an integer, let $|\Phi_d\rangle=d^{-1/2}\sum_{j=1}^d|j\rangle\otimes|j\rangle$, and let $\eta\in\mathbb R$ make $W_d^\eta=(1-\eta)I/d^2+\eta|\Phi_d\rangle\langle\Phi_d|$ a density operator. Equivalently, $-1/(d^2-1)\le\eta\le1$. Write $H_d=\sum_{j=1}^d1/j$ for the finite harmonic number. Then, for all local projective measurements,
--
--   $$
--   W_d^\eta\text{ is steerable from Alice to Bob}
--   \quad\Longleftrightarrow\quad
--   \eta>\frac{H_d-1}{d-1}.
--   $$
--
--   Equality is nonsteerable. The hidden ensemble is shared by all Alice settings and may contain arbitrary mixed states and continuous mixtures.
--
--   This gives the exact isotropic projective steering boundary. The accepted library's isotropic density is precisely Eq. (12).
-- source:
--   Steering, Entanglement, Nonlocality, and the EPR Paradox, arXiv:quant-ph/0612147v3, PDF p. 3, (ii) Isotropic States: exact projective steering threshold

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P62

noncomputable section

open MeasureTheory

open scoped BigOperators Matrix.Norms.Elementwise

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

namespace QAlgorithms.Papers.Independent.Intakethird100.P62

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] QAlgorithms.Papers.Independent.Intakethird100.P62.matrixContinuousENorm

attribute [local instance] QAlgorithms.Papers.Independent.Intakethird100.P62.matrixMeasurable

/-- arXiv:quant-ph/0612147v3, PDF pp.3--4, (12)--(15): exact isotropic
projective-steering threshold. The accepted isotropic density uses the same-index
maximally entangled vector from (12). No incorrect arbitrary-complex-basis
identity from (13), and no defective auxiliary bound (14), is assumed. -/
theorem isotropic_threshold (d : ℕ) (hd : 2 ≤ d) (eta : ℝ)
    (hphysical : IsDensityMatrix
      (QAlgorithms.Papers.Independent.Information100.P60.isotropic d eta)) :
    Steerable (QAlgorithms.Papers.Independent.Information100.P60.isotropic d eta) ↔
      ((harmonic d : ℝ) - 1) / ((d : ℝ) - 1) < eta := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P62

end
