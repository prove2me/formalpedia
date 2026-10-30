-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P32_chainUncrossing
-- name    : QAlgorithms.Papers.Independent.Extend50.P32.chainUncrossing
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:05:37.399189+00:00
-- url     : https://prove2.me/theorems/30dc6f44-ce3d-4e54-ae09-819030089caf
-- title:
--   Lemma 6.2: Uncrossing a family of increasing chains
-- statement:
--   Let $b$ be a distinct-letter word over a linearly ordered alphabet. Embed its finite alphabet in the real line in order, and place its letters at their occurrence positions. Let $I_1,\ldots,I_c$ be disjoint increasing chains, allowing $c=0$ and empty chains. Curves are graphs of continuous strictly increasing functions tending to $\pm\infty$ at the corresponding ends. Then the selected occurrences can be regrouped so that
--
--   $$
--   \bigcup_{a=1}^c I_a^\prime=\bigcup_{a=1}^c I_a,\qquad I_1^\prime,\ldots,I_c^\prime\text{ are disjoint increasing chains admitting disjoint proper increasing curves}.
--   $$
--
--   This isolates the source comparison or construction with all of its domain and occurrence conventions retained.
-- source:
--   Efficient quantum tomography II, arXiv:1612.00034v1, PDF p. 28, Lemma 6.2

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P32

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal Matrix ComplexOrder Topology

namespace QAlgorithms.Papers.Independent.Extend50.P32

open QAlgorithms.Papers.Independent.Support50.P38 (wordMass tv)

-- For the density matrices below, the characteristic-polynomial identity
-- preserves all eigenvalues with multiplicity and is equivalent to unitary
-- diagonalization with these real eigenvalues. No accuracy is assumed.

open QAlgorithms.Papers.Independent.Gap20.P17 (HasSpectrum)

/-- Lemma 6.2, PDF pp.28,30,32: uncrossing, with no admissibility or
separation premise; c=0 and empty chains are allowed. -/
theorem chainUncrossing {A : Type*} [LinearOrder A] (b : List A) (hDistinct : b.Nodup)
    (e : A → ℝ) (hEmbedding : StrictMonoOn e (↑b.toFinset : Set A)) (c : ℕ)
    (I : Fin c → Finset (Fin (wordPoints b).length)) (hChains : IsChains (wordPoints b) I) :
    ∃ J : Fin c → Finset (Fin (wordPoints b).length),
      IsChains (wordPoints b) J ∧ Finset.univ.biUnion J = Finset.univ.biUnion I ∧
      ∃ f : Fin c → ℝ → ℝ, CurvesThrough e (wordPoints b) J f := by sorry

end QAlgorithms.Papers.Independent.Extend50.P32

end
