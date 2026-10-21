-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P15_pBanach_james_blocks
-- name    : QAlgorithms.Papers.Independent.Support21.P15.pBanach_james_blocks
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T04:35:52.122003+00:00
-- url     : https://prove2.me/theorems/43d8e7c5-6eb8-4ab5-a23b-55eca93c9158
-- title:
--   James distortion for p-Banach spaces
-- statement:
--   Let $0<p\le1$, and let $X$ be a complex p-Banach space with a basis $(x_j)_{j\ge1}$ equivalent to the unit basis of $\ell_p$. For every $\varepsilon>0$, there are nonempty finite scalar coefficient blocks $(c_{n,j})_j$, with the support of each block strictly before the support of the next, such that the basic sequence
--
--   $$
--   y_n=\sum_j c_{n,j}x_j
--   $$
--
--   is $(1+\varepsilon)$-equivalent to the unit basis of $\ell_p$. Explicitly, for some $a,b>0$ with $b/a\le1+\varepsilon$, every finitely supported complex sequence $(t_n)$ satisfies $a(\sum_n|t_n|^p)^{1/p}\le\|\sum_n t_n y_n\|\le b(\sum_n|t_n|^p)^{1/p}$.
--
--   This is the successive-block distortion statement used in the proof of Lemma 3.2. **Formalization Note** The initial basis is expressed by finite-coefficient equivalence and density of its finite linear span in $X$. The resulting sequence is a basis of its closed span; it need not span all of $X$.
-- source:
--   On subspaces of non-commutative L_p-spaces, arXiv:math/0307169v1, PDF p. 15, Unnumbered p-Banach James distortion extension

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P15

noncomputable section

open scoped BigOperators

open Filter

namespace QAlgorithms.Papers.Independent.Support21.P15

/-- Unnumbered p-Banach James distortion extension, arXiv:math/0307169v1,
PDF p.15: a basis equivalent to ell_p admits arbitrarily nearly isometric
successive block basic sequences, for 0<p≤1. The dense-span condition asserts
that the initial sequence is a basis of the whole space. -/
theorem pBanach_james_blocks
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (g : ComplexQuasiNorm E) (hE : IsSourcePBanach p g)
    (b : ℕ → E) (hBasis : GaugeSpanning g b)
    (hEquivalent : ∃ K : ℝ, 1 ≤ K ∧ EquivalentLp p K g b) :
    ∀ eps : ℝ, 0 < eps → ∃ c : ℕ → (ℕ →₀ ℂ),
      SuccessiveBlocks c ∧
      EquivalentLp p (1 + eps) g (fun n => coefficientVector b (c n)) := by sorry

end QAlgorithms.Papers.Independent.Support21.P15

end
