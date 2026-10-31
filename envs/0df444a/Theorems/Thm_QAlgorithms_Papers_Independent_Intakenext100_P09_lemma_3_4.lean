-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P09_lemma_3_4
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P09.lemma_3_4
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:13:55.143527+00:00
-- url     : https://prove2.me/theorems/91e84157-314b-422c-a85b-8fc5827101f3
-- title:
--   Lemma 3.4
-- statement:
--   Let $X$ be any topological space, $V$ an abelian topological group, and $p\ge0$. Set $E_p=C(X^{p+1},V)$ as an abelian group. Currying identifies the column $A^{p,q}(X;V)$ with all functions $X^{q+1}\to E_p$. Let $d$ be the alternating deletion differential and let $\epsilon:E_p\to A^{p,0}(X;V)$ send $c$ to the cochain constant in its second block. Then
--
--   $$0\longrightarrow E_p\xrightarrow{\epsilon}A^{p,0}(X;V)\xrightarrow{d}A^{p,1}(X;V)\xrightarrow{d}\cdots$$
--
--   is exact, including injectivity of $\epsilon$. The vertical sign $(-1)^p$ in the double complex changes neither kernels nor images.
--
--   **Source correction.** The printed unqualified exactness is read as naturally augmented exactness, as its insertion proof requires. For a point $X$ and $V=\mathbb Z$, the nonaugmented $H^0$ is $\mathbb Z$, rather than zero. If $X$ is empty, $E_p$ and all nonnegative column groups are zero, so no extra nonemptiness hypothesis is needed.
-- source:
--   A Spectral Sequence Connecting Continuous With Locally Continuous Group Cohomology, arXiv:1110.0994v1, PDF p. 8, Lemma 3.4

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P09

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P09

universe u v w

/-- PDF p. 8, Lemma 3.4, with the degree-zero correction forced by its
insertion proof: the naturally augmented column is exact. The printed
unqualified exactness would make the nonaugmented H^0 zero; for X a point
and V = Z it is Z. Currying identifies the coefficient group with
C(X^(p+1), V). The unsigned second-block differential differs from the
paper's signed vertical differential by the invertible scalar (-1)^p,
which does not change any kernel or image. No nonemptiness of X is added:
when X is empty this coefficient group and every column group are zero. -/
theorem lemma_3_4 {X : Type u} {V : Type v} [TopologicalSpace X]
    [TopologicalSpace V] [AddCommGroup V] [IsTopologicalAddGroup V] :
    ∀ p : ℕ, Function.Injective (columnAugmentation (X := X) (V := V) p) ∧
      (columnAugmentation (X := X) (V := V) p).range =
        (differential (X := X) (V := ColumnCoefficients X V p) 0).ker ∧
      (∀ q : ℕ, (differential (X := X) (V := ColumnCoefficients X V p) q).range =
        (differential (X := X) (V := ColumnCoefficients X V p) (q + 1)).ker) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P09

end
