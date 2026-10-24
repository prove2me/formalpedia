-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P31_depolarizingSubsetExpansion
-- name    : QAlgorithms.Papers.Independent.Support50.P31.depolarizingSubsetExpansion
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:34:00.482444+00:00
-- url     : https://prove2.me/theorems/5cb9073c-2aed-481a-8733-4c1fc3da2ba1
-- title:
--   Expansion of a depolarizing product into subset resets
-- statement:
--   Let $n\ge1$, let $d_i\ge1$, and choose $0<p_i<1$. Define $D_i(X)=(1-p_i)X+(p_i/d_i)\operatorname{Tr}(X)I_i$ on the operators of a $d_i$-dimensional complex Hilbert space. For each subset $L\subseteq\{1,\ldots,n\}$, let $E_L$ be the tensor product whose $i$-th factor is $X\mapsto\operatorname{Tr}(X)I_i/d_i$ when $i\in L$, and the identity map otherwise. Then, on every joint operator $X$,
--   $$
--   \left(\bigotimes_{i=1}^nD_i\right)(X)
--   =\sum_{L\subseteq\{1,\ldots,n\}}
--    \left(\prod_{i\in L}p_i\prod_{i\notin L}(1-p_i)\right)E_L(X).
--   $$
--   All tensor maps are their full linear matrix-unit extensions, so this is an identity on arbitrary operators, including entangled density matrices. The expansion separates the channel into actual subset-reset maps.
-- source:
--   On some additivity problems in quantum information theory, arXiv:math-ph/0003002v2, PDF p. 10, §5, equation (20): actual tensor-channel expansion

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P31

noncomputable section

open Filter Asymptotics

open scoped ComplexConjugate ENNReal

namespace QAlgorithms.Papers.Independent.Support50.P31

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P63 (schatten)

open QAlgorithms.Papers.Independent.Gap48.P03 (holevoQuantity)

open QAlgorithms.Papers.Independent.Claimed50.P38 (tensorSuperop)

open QAlgorithms.Papers.Independent.Dependency50.P44 (tensorChannels)

/-- PDF p.10, (20): actual tensor-map expansion on every operator. No restriction
to product densities or minimum-rank hypothesis on arbitrary projections. -/
theorem depolarizingSubsetExpansion {n : ℕ} (hn : 0 < n) (d : Fin n → ℕ) (hd : ∀ i, 0 < d i)
    (p : Fin n → ℝ) (hp : ∀ i, 0 < p i ∧ p i < 1)
    (X : Matrix ((i : Fin n) → Fin (d i)) ((i : Fin n) → Fin (d i)) ℂ) :
    depolarizingProduct d hd p X =
      ∑ L : Finset (Fin n), (depolarizingSubsetCoefficient p L : ℂ) • subsetExpectation d hd L X := by sorry

end QAlgorithms.Papers.Independent.Support50.P31

end
