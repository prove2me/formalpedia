-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P62_werner_threshold
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P62.werner_threshold
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:30:59.744466+00:00
-- url     : https://prove2.me/theorems/3f2b42da-1b55-42ed-ac39-4a68efe8cd22
-- title:
--   Exact projective steering threshold of Werner states
-- statement:
--   Let $d\ge2$ be an integer and let $\eta\in\mathbb R$ make the following operator a density matrix on $\mathbb C^d\otimes\mathbb C^d$:
--
--   $$
--   W_d^\eta=\frac{d-1+\eta}{d-1}\frac{I}{d^2}-\frac{\eta}{d-1}\frac{F}{d},
--   \qquad F(u\otimes v)=v\otimes u.
--   $$
--
--   The physical parameter interval is $-(d-1)/(d+1)\le\eta\le1$. With all local projective measurements allowed, and arbitrary mixed or pure hidden quantum states in a common continuous LHS ensemble,
--
--   $$
--   W_d^\eta\text{ is steerable from Alice to Bob}
--   \quad\Longleftrightarrow\quad
--   \eta>1-\frac1d.
--   $$
--
--   Equality is nonsteerable. This identifies the exact projective steering boundary, including the physical negative-parameter range.
-- source:
--   Steering, Entanglement, Nonlocality, and the EPR Paradox, arXiv:quant-ph/0612147v3, PDF p. 3, (i) Werner States: exact projective steering threshold

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P62

noncomputable section

open MeasureTheory

open scoped BigOperators Matrix.Norms.Elementwise

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

namespace QAlgorithms.Papers.Independent.Intakethird100.P62

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] QAlgorithms.Papers.Independent.Intakethird100.P62.matrixContinuousENorm

attribute [local instance] QAlgorithms.Papers.Independent.Intakethird100.P62.matrixMeasurable

/-- arXiv:quant-ph/0612147v3, PDF p.3, (8)--(11) and the definition of
eta_steer above (9). The iff uses all projective observables; equality is
nonsteerable. The defective auxiliary single-outcome (10) is not assumed. -/
theorem werner_threshold (d : ℕ) (hd : 2 ≤ d) (eta : ℝ)
    (hphysical : IsDensityMatrix (wernerEta d eta)) :
    Steerable (wernerEta d eta) ↔ 1 - 1 / (d : ℝ) < eta := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P62

end
