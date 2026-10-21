-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P16_occupation_basis
-- name    : QAlgorithms.Papers.Independent.Support21.P16.occupation_basis
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T04:37:56.040906+00:00
-- url     : https://prove2.me/theorems/ef06ab00-0875-4653-82b7-6e666ff3c389
-- title:
--   Explicit occupation basis and symmetric dimension
-- statement:
--   Let $d>0$ and $n\ge1$ be integers, and let $H_n^+\subset(\mathbb C^d)^{\otimes n}$ be the permutation-fixed Bose subspace with projector $s_n$. Occupations are tuples $o=(o_1,\ldots,o_d)$ of nonnegative integers with $\sum_a o_a=n$. Define $|o\rangle$ in tensor-word coordinates to have amplitude $\sqrt{\prod_a o_a!/n!}$ on each word with occupation $o$, and zero elsewhere. These explicit vectors form an orthonormal basis of $H_n^+$, and for every $\phi\in\mathbb C^d$,
--   $$
--   \phi^{\otimes n}=\sqrt{n!}\sum_{\sum_a o_a=n}
--   \left(\prod_{a=1}^d\frac{\phi_a^{o_a}}{\sqrt{o_a!}}\right)|o\rangle,
--   \qquad \dim H_n^+=\#\{o:\textstyle\sum_a o_a=n\}=\binom{d+n-1}{n}.
--   $$
--   The embedding $E_n$ whose columns are $|o\rangle$ has real entries and satisfies $E_n^*E_n=I$ and $E_nE_n^*=s_n$.
--
--   This provides real orthonormal occupation coordinates, their concrete isometric embedding, and the correct symmetric dimensions.
-- source:
--   Optimal Cloning of Pure States, arXiv:quant-ph/9804001v1, PDF p. 5, occupation-basis

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P16

noncomputable section

open scoped Matrix ComplexOrder

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Support21.P16

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

open QAlgorithms.Papers.Independent.Renew46.P45
  (TensorMat boseProjector powerVector IsCloningCovariant haarAverage)

attribute [local instance] QAlgorithms.Papers.Independent.Support21.P16.unitaryMeasurable

/-- PDF p.5 Eqs.(3.1)–(3.2): actual normalized occupation vectors, full expansion,
real isometric embedding and symmetric dimension. The printed missing '+'
on H before (3.2) is read as Bose space, as its basis and count require. -/
theorem occupation_basis (d n : ℕ) (hd : 0 < d) (hn : 1 ≤ n) :
    Orthonormal ℂ (occupationKet d n) ∧
    Submodule.span ℂ (Set.range (occupationKet d n)) = boseSpace d n ∧
    (∀ phi : EuclideanSpace ℂ (Fin d), coherentTensor n phi =
      ∑ o : BoseOccupation d n, occupationCoefficient phi o • occupationKet d n o) ∧
    Module.finrank ℂ (boseSpace d n) = boseDimension d n ∧
    Fintype.card (BoseOccupation d n) = boseDimension d n ∧
    (∀ x o, (occupationEmbedding d n x o).im = 0) ∧
    (occupationEmbedding d n)ᴴ * occupationEmbedding d n = 1 ∧
    occupationEmbedding d n * (occupationEmbedding d n)ᴴ = boseProjector d n := by sorry

end QAlgorithms.Papers.Independent.Support21.P16

end
