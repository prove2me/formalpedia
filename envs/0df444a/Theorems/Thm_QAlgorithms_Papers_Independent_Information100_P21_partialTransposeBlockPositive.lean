-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P21_partialTransposeBlockPositive
-- name    : QAlgorithms.Papers.Independent.Information100.P21.partialTransposeBlockPositive
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:45:42.793829+00:00
-- url     : https://prove2.me/theorems/2d0cd1f8-a7d1-4172-9860-e6178ee704e0
-- title:
--   II.1 — Lemma II.1 (Block positivity of a partial transpose). If ρ ⪰ 0 and A = ρΓ , then A is block-positive. More explicitly,
-- statement:
--   Let $\rho\succeq0$ act on two qubits, and let $e,f$ be arbitrary local vectors, with no normalization required. Entrywise conjugation is in the basis defining the second-factor partial transpose $\Gamma$. Then
--   $$\langle e\otimes f|\rho^\Gamma|e\otimes f\rangle=\langle e\otimes\overline f|\rho|e\otimes\overline f\rangle\ge0.$$
--   This is block positivity of the partial transpose.
-- source:
--   The Minimal Dimension of Entangled -Noise Advantage, arXiv:2609.28367v1, PDF p. 6, II.1 — Lemma II.1 (Block positivity of a partial transpose). If ρ ⪰ 0 and A = ρΓ , then A is block-positive. More explicitly,

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Information100.P21

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arxiv:2609.28367v1, PDF p. 6, Lemma II.1 (Block positivity of a partial transpose). If ρ ⪰ 0 and A = ρΓ , then A is block-positive. More explicitly,. -/
theorem partialTransposeBlockPositive (rho : Op QQ) (h : rho.PosSemidef) (e f : Vec (Fin 2)) :
  quad (pt rho) (tensor e f) = quad rho (tensor e (conjugate f)) ∧
    0 ≤ quad (pt rho) (tensor e f) := by sorry

end QAlgorithms.Papers.Independent.Information100.P21

end
