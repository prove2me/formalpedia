-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P12_finite_center_generator_fraction
-- name    : QAlgorithms.Papers.Independent.Next46.P12.finite_center_generator_fraction
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T13:09:37.963597+00:00
-- url     : https://prove2.me/theorems/785c4f19-c319-43ea-a1e9-a1ee1c54bf73
-- title:
--   Remark 2.2(b): finite-field generator fraction
-- statement:
--   Let $A$ be a finite-dimensional split semisimple unital algebra over a field $k$. Choose a split presentation $A\cong\prod_{\lambda\in I}\operatorname{End}_k(V^\lambda)$, where the $V^\lambda$ are all its nonzero simple left modules, one per isomorphism class. Let $\epsilon(\lambda)$ be the inverse image of identity in block $\lambda$ and zero in the other blocks. For $z\in Z(A)$ write $a_\lambda$ for its scalar on $V^\lambda$, and let $\chi^\lambda(a)=\operatorname{tr}(a|_{V^\lambda})$. Assume $k$ is finite, with $q=|k|$, and put $m=|I|$. Uniform choice from the finite set $Z(A)$ gives
--
--   $$\Pr[k[z]=Z(A)]=\frac{|\{z\in Z(A):k[z]=Z(A)\}|}{|Z(A)|}=\frac{\prod_{i=0}^{m-1}(q-i)}{q^m}=\prod_{i=0}^{m-1}\left(1-\frac{i}{q}\right).$$
--
--   For each fixed $m$, the last numerical expression tends to $1$ as the natural number $q$ tends to infinity. No restriction $q\ge m$ is imposed on the finite-field formula.
--
--   This counts center generators and records the asymptotic behavior of the displayed numerical function.
-- source:
--   Canonical idempotents of multiplicity-free families of algebras, arXiv:1606.08900v5, PDF p. 8, Remark 2.2(b): finite-field generator fraction

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P12

noncomputable section

open scoped BigOperators Classical

open Filter

namespace QAlgorithms.Papers.Independent.Next46.P12

universe u v w

variable {k : Type u} [Field k]

variable {A : Type v} [Ring A] [Algebra k A]

/-- Remark 2.2(b), source PDF p. 8. Counting is uniform on the finite center.
The limit concerns the displayed numerical function, with block count fixed. -/
theorem finite_center_generator_fraction [FiniteDimensional k A] [Finite k]
    (D : SplitPresentation k A) :
    finiteGeneratorProbability D =
      (∏ i ∈ Finset.range (Fintype.card D.Label), ((Nat.card k : ℝ) - (i : ℝ))) /
        (Nat.card k : ℝ) ^ Fintype.card D.Label ∧
    finiteGeneratorProbability D = generatorFraction (Fintype.card D.Label) (Nat.card k) ∧
    Tendsto (generatorFraction (Fintype.card D.Label)) atTop (nhds 1) := by sorry

end QAlgorithms.Papers.Independent.Next46.P12

end
