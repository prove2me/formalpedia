-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P35_tensorPower_concave
-- name    : QAlgorithms.Papers.Independent.Dependency50.P35.tensorPower_concave
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:11:20.29768+00:00
-- url     : https://prove2.me/theorems/f6a49a18-8721-4f89-af36-8329fd387d8b
-- title:
--   Lemma 16: operator concavity of tensor powers
-- statement:
--   Let $\beta\in[0,1]$ and define $F(L,R)=L^\beta\otimes(R^T)^{1-\beta}$ for PSD operators $L,R$ on the same finite-dimensional complex space. Then for any PSD $L_1,L_2,R_1,R_2$ and $\lambda\in[0,1]$,
--
--   $$
--   F(\lambda L_1+(1-\lambda)L_2,\lambda R_1+(1-\lambda)R_2)\ge\lambda F(L_1,R_1)+(1-\lambda)F(L_2,R_2)
--   $$
--
--   in the Loewner order. Transpose is in the fixed basis, and zero powers are the identity, including on the kernel. This is joint operator concavity; the proof's reversed displayed inequality is not used.
-- source:
--   On quantum Renyi entropies: a new generalization and some properties, arXiv:1306.3142v4, PDF p. 21, Lemma 16

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

open Filter Topology

namespace QAlgorithms.Papers.Independent.Dependency50.P35

attribute [local instance] Classical.propDecidable Classical.decEq

-- Reuse the accepted matrix type and positive-operator Schatten expression.

open QAlgorithms.Papers.Independent.Information100.P63 (Mat schatten)

open QAlgorithms.Papers.Independent.Information100.P58 (Distribution)

/-- PDF p.21, Lemma 16: the Loewner concavity direction (the proof display
prints the reverse direction). Singular inputs and beta endpoints are included. -/
theorem tensorPower_concave {I : Type} [Fintype I] [DecidableEq I]
    (b : ℝ) (hb : 0 ≤ b ∧ b ≤ 1) (L1 L2 R1 R2 : Mat I)
    (hL1 : L1.PosSemidef) (hL2 : L2.PosSemidef)
    (hR1 : R1.PosSemidef) (hR2 : R2.PosSemidef)
    (l : ℝ) (hl : 0 ≤ l ∧ l ≤ 1) :
    (concaveTensor b ((l : ℂ) • L1 + ((1-l : ℝ) : ℂ) • L2)
      ((l : ℂ) • R1 + ((1-l : ℝ) : ℂ) • R2) -
      ((l : ℂ) • concaveTensor b L1 R1 + ((1-l : ℝ) : ℂ) • concaveTensor b L2 R2)).PosSemidef := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P35

end
