-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P07_productProtection_rigidity
-- name    : QAlgorithms.Papers.Independent.Information100.P07.productProtection_rigidity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:36:02.710994+00:00
-- url     : https://prove2.me/theorems/a9adcf07-ff25-4dbe-b6ed-05865617296f
-- title:
--   Lemma S3: qutrit product rigidity and one-sided completion
-- statement:
--   Let $(K_i)$ be a product Kraus family of a CPTP channel on two qutrits, protecting a $2\times2$ rectangle $L=U\otimes V$ by scaled product unitaries with probabilities $p_i$. Suppose it protects $E\supseteq L$ by scaled unitaries with the same probabilities. Then
--   $$r(E)=(3,3)\Longrightarrow\text{every nonzero }K_i\text{ is a scalar product unitary on the full space}.$$
--   All zero-weight operators then vanish globally. If $r(E)=(2,3)$, product protection extends with the same weights to $U\otimes\mathbb C^3$. If $r(E)=(3,2)$, it extends to $\mathbb C^3\otimes V$. Protection with these weights on a strict enlargement of either protected one-sided rectangle likewise forces the full-space conclusion, including globally zero zero-weight terms.
--
--   The local ranks here are computed from partial traces of subspace projectors.
-- source:
--   Complete Classification of Reversible Entanglement Transformations of Two Qutrits, arXiv:2610.05234v1, PDF p. 11, Lemma S3: qutrit product rigidity and one-sided completion

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P07

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P07

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms QAlgorithms.Entanglement

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arXiv:2610.05234v1, PDF p.11, Lemma S3: both one-sided cases and strict extensions. -/
theorem productProtection_rigidity {m : ℕ} (K : Fin m → Joint) (p : Fin m → ℝ)
    (P Q : Local) (E : Submodule ℂ Space) (hK : IsKrausFamily K)
    (hprod : ∀ i, IsProduct (K i)) (hP : IsProjection P) (hQ : IsProjection Q)
    (hrP : P.rank = 2) (hrQ : Q.rank = 2)
    (hL : ProductProtects K P Q p) (hLE : operatorRange (Matrix.kronecker P Q) ≤ E)
    (hE : Protects K E p) :
    (localRanks E = (3, 3) → (∀ i, ScalarProductUnitary (K i)) ∧ (∀ i, p i = 0 → K i = 0)) ∧
    (localRanks E = (2, 3) → ProductProtects K P 1 p) ∧
    (localRanks E = (3, 2) → ProductProtects K 1 Q p) ∧
    (∀ F : Submodule ℂ Space,
      ((operatorRange (Matrix.kronecker P (1 : Local)) < F ∧ ProductProtects K P 1 p) ∨
       (operatorRange (Matrix.kronecker (1 : Local) Q) < F ∧ ProductProtects K 1 Q p)) →
      Protects K F p → (∀ i, ScalarProductUnitary (K i)) ∧ (∀ i, p i = 0 → K i = 0)) := by sorry

end QAlgorithms.Papers.Independent.Information100.P07

end
