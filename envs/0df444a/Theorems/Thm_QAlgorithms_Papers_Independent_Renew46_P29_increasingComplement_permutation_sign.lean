-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P29_increasingComplement_permutation_sign
-- name    : QAlgorithms.Papers.Independent.Renew46.P29.increasingComplement_permutation_sign
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T21:00:20.725978+00:00
-- url     : https://prove2.me/theorems/6c870af6-5ec0-4849-8718-cd5ed4f2a3cf
-- title:
--   The sign of an increasing-complement permutation
-- statement:
--   Let $n\geq 0$, let $1\leq i\leq n$, and let $\sigma$ be a permutation of $\{1,\ldots,n+1\}$. Write $k=\sigma(1)$ and $\ell=\sigma(i+1)$, and assume $k<\ell$. If the restriction of $\sigma$ to the complement of $\{1,i+1\}$ is increasing, then
--
--   $$\operatorname{sgn}(\sigma)=(-1)^{i+k+\ell}.$$
--
--   This sign controls the alternating terms in the Alexander–Spanier differentiation calculation. **Formalization Note** Lean uses zero-based indices; the two image indices are increased by one in the exponent. The complements use $n+1$ elements, as required by the application on PDF p. 60.
-- source:
--   Abelian extensions of infinite-dimensional Lie groups, arXiv:math/0402303v1, PDF p. 58, Lemma A.5

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P29

namespace QAlgorithms.Papers.Independent.Renew46.P29

open Set Filter Topology

universe u v

/-- Lemma A.5, PDF p. 58 (with its application on p. 60): the complement
is taken in all n+1 positions, correcting the printed n. Fin uses zero-based
indices: i is the paper's i, while k and ell are the two images plus one.
The strict inequality makes the two distinguished positions distinct. -/
theorem increasingComplement_permutation_sign
    (n : ℕ) (sigma : Equiv.Perm (Fin (n + 1)))
    (i : Fin (n + 1)) (hi : i ≠ 0)
    (hOrder : sigma 0 < sigma i)
    (hIncreasing : StrictMonoOn sigma {j : Fin (n + 1) | j ≠ 0 ∧ j ≠ i}) :
    Equiv.Perm.sign sigma =
      (-1 : ℤˣ) ^ (i.val + (sigma 0).val + 1 + (sigma i).val + 1) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P29
