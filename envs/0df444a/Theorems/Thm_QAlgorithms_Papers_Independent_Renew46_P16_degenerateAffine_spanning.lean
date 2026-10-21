-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P16_degenerateAffine_spanning
-- name    : QAlgorithms.Papers.Independent.Renew46.P16.degenerateAffine_spanning
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T20:19:48.25339+00:00
-- url     : https://prove2.me/theorems/1458d0de-b74c-4e48-aa3a-0bffe307de31
-- title:
--   Lemma 6.11 — spanning the degenerate affine BMW tower
-- statement:
--   Let $S$, $\Omega$, and $W_n^{\mathrm{aff}}$ be as in Definition 6.7. For every $n\ge1$, interpreting smaller algebras through their canonical generator images,
--
--   $$W_n^{\mathrm{aff}}=\operatorname{span}_S\!\left(W_{n-1}^{\mathrm{aff}}\ \cup\ \{a\chi b:a,b\in W_{n-1}^{\mathrm{aff}},\ \chi\in C_n\}\right),$$
--
--   where $C_n=\{e_{n-1},s_{n-1}\}\cup\{x_n^a:a\ge1\}$ for $n\ge2$, and $C_1=\{x_1^a:a\ge1\}$. At level zero the canonical image is the scalar subalgebra.
--
--   The equality expresses the source's containment in a linear span: the reverse containment follows because every displayed element is in the ambient algebra.
-- source:
--   On Cellular Algebras with Jucys Murphy Elements, arXiv:0907.3459v2, PDF p. 24, Lemma 6.11

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P16

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Renew46.P16

/-- Lemma 6.11, PDF p.24. Every element lies in the S-linear span of the
previous-level image and products a chi b; the n=1 convention is explicit. -/
theorem degenerateAffine_spanning (S : Type*) [CommRing S] (omega : ℕ → S)
    (n : ℕ) (hn : 1 ≤ n) :
    Submodule.span S
      ((affineLevel S omega n (n - 1) : Set (AffineBMW S omega n)) ∪
        {z | ∃ a ∈ affineLevel S omega n (n - 1),
          ∃ b ∈ affineLevel S omega n (n - 1),
            ∃ chi ∈ middleFactors S omega n, z = a * chi * b}) = ⊤ := by sorry

end QAlgorithms.Papers.Independent.Renew46.P16

end
