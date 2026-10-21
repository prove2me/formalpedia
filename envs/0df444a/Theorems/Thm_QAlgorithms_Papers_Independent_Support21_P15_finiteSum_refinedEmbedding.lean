-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P15_finiteSum_refinedEmbedding
-- name    : QAlgorithms.Papers.Independent.Support21.P15.finiteSum_refinedEmbedding
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T04:35:09.08356+00:00
-- url     : https://prove2.me/theorems/a2937562-fbb6-445e-abea-b691a136b80a
-- title:
--   Simultaneous normalized-column refinement of finite p-sum embeddings
-- statement:
--   Let $0<p<\infty$ and $K\ge1$. Let $X$ be a complex Banach space when $p\ge1$, or a complex p-Banach space when $p<1$, and let $F$ be a finite-dimensional complex quasi-normed space. Suppose that for every integer $N\ge1$ there is a K-isomorphic linear embedding of $\ell_p^N(F)$ into $X$. For every $\varepsilon>0$ and $n\ge1$, there is a single K-isomorphic embedding $T:\ell_p^n(F)\to X$ such that, for every nonzero $x\in F$, the vectors
--
--   $$
--   v_i(x)=\frac{T(e_i\otimes x)}{\|T(e_i\otimes x)\|},\qquad 1\le i\le n,
--   $$
--
--   are $(1+\varepsilon)$-equivalent to the unit basis of $\ell_p^n$. Here equivalence means that there are positive constants $a,b$ with $b/a\le1+\varepsilon$ such that $a\|(c_i)\|_p\le\|\sum_i c_i v_i(x)\|\le b\|(c_i)\|_p$ for every complex coefficient vector; these constants may depend on $x$.
--
--   If $p\ge1$ and the original K-isomorphic copies can all be chosen C-complemented in $X$ for one constant $C\ge0$, then the refined embeddings can be chosen so that their ranges are KC-complemented in $X$, while satisfying the same simultaneous property.
--
--   This refines uniform finite-sum containment without changing its embedding distortion. **Formalization Note** Completeness and all bounds use the specified quasi-norm directly. The printed final domain $\ell_p(F)$ is read as the already-declared finite domain $\ell_p^n(F)$.
-- source:
--   On subspaces of non-commutative L_p-spaces, arXiv:math/0307169v1, PDF p. 15, Lemma 3.2

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P15

noncomputable section

open scoped BigOperators

open Filter

namespace QAlgorithms.Papers.Independent.Support21.P15

/-- Lemma 3.2, arXiv:math/0307169v1, PDF p.15: a single K-embedding works for
all nonzero x in F after separate column normalization. Both the ordinary and
C-complemented assertions are retained, with bound KC in the latter.
The final printed domain ell_p(F) is read as the already declared ell_p^n(F).
No p≠2 restriction or ambient operator algebra is assumed. -/
theorem finiteSum_refinedEmbedding
    {E F : Type*} [AddCommGroup E] [Module ℂ E]
    [AddCommGroup F] [Module ℂ F] [FiniteDimensional ℂ F]
    (p K : ℝ) (hp : 0 < p) (hK : 1 ≤ K)
    (gE : ComplexQuasiNorm E) (gF : ComplexQuasiNorm F)
    (hE : IsSourcePBanach p gE)
    (hCopies : ∀ n : ℕ, 1 ≤ n → ∃ T : (Fin n → F) →ₗ[ℂ] E,
      FiniteLpEmbedding p K gF gE T) :
    (∀ eps : ℝ, 0 < eps → ∀ n : ℕ, 1 ≤ n →
      ∃ T : (Fin n → F) →ₗ[ℂ] E, RefinedFiniteEmbedding p K eps gF gE T) ∧
    (∀ C : ℝ, 0 ≤ C → 1 ≤ p →
      (∀ n : ℕ, 1 ≤ n → ∃ T : (Fin n → F) →ₗ[ℂ] E,
        FiniteLpEmbedding p K gF gE T ∧ ComplementedRange gE C T) →
      ∀ eps : ℝ, 0 < eps → ∀ n : ℕ, 1 ≤ n →
        ∃ T : (Fin n → F) →ₗ[ℂ] E,
          RefinedFiniteEmbedding p K eps gF gE T ∧ ComplementedRange gE (K * C) T) := by sorry

end QAlgorithms.Papers.Independent.Support21.P15

end
