-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P32_admissibleChainLifting
-- name    : QAlgorithms.Papers.Independent.Extend50.P32.admissibleChainLifting
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:04:41.965978+00:00
-- url     : https://prove2.me/theorems/f1b070df-a4c3-4269-a13f-19348bff2833
-- title:
--   Theorem 6.1: Admissible chain lifting through one RSK bump
-- statement:
--   Let $w$ be a distinct-letter word over a linearly ordered alphabet, and let $b$ be the computed word bumped from its first row into its second row. Embed the finite alphabet in the real line in order. White points use positions in $w$; black points keep the input times when their letters are bumped, rather than fresh positions in $b$. Let $c\ge1$ and let $I_1,\ldots,I_c$ be disjoint increasing chains in $b$, all using admissible letters $S\subseteq\operatorname{letters}(b)$. Invariant (19) says that there are pairwise disjoint graphs of continuous strictly increasing functions tending to $\pm\infty$, passing through the associated chains, with every inadmissible point strictly southeast of the southeasternmost graph. Then there are an admissible set $S^\prime$, an integer $\Delta\ge0$, and $c$ disjoint admissible increasing chains $J_1,\ldots,J_c$ in $w$ such that
--
--   $$
--   S\subseteq S^\prime\subseteq\operatorname{letters}(w),\quad |S^\prime|=|S|+\Delta,\quad\sum_{a=1}^c|J_a|=\sum_{a=1}^c|I_a|+\Delta,\quad\text{invariant (19) holds for }(w,S^\prime,J).
--   $$
--
--   This isolates the source comparison or construction with all of its domain and occurrence conventions retained.
-- source:
--   Efficient quantum tomography II, arXiv:1612.00034v1, PDF p. 28, Theorem 6.1

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

/-- Theorem 6.1, PDF pp.28-30: all cardinality, length, containment,
admissibility, and separation conclusions. The input bump word is computed
from w. Its black-point coordinates are inherited bump times in w, not a
fresh indexing; e need embed only the finite alphabet present in w. -/
theorem admissibleChainLifting {A : Type*} [LinearOrder A] (w : List A)
    (hDistinct : w.Nodup) (e : A → ℝ) (hEmbedding : StrictMonoOn e (↑w.toFinset : Set A))
    (c : ℕ) (hc : 1 ≤ c) (admissible : Finset A)
    (hAdmissible : admissible ⊆ ((firstBumpPoints w).map Prod.snd).toFinset)
    (I : Fin c → Finset (Fin (firstBumpPoints w).length))
    (hInvariant : AdmissibleChains e (firstBumpPoints w) admissible I) :
    ∃ (newAdmissible : Finset A) (delta : ℕ)
      (J : Fin c → Finset (Fin (wordPoints w).length)),
      admissible ⊆ newAdmissible ∧ newAdmissible ⊆ w.toFinset ∧
      newAdmissible.card = admissible.card + delta ∧
      (∑ j, (J j).card) = (∑ j, (I j).card) + delta ∧
      AdmissibleChains e (wordPoints w) newAdmissible J := by sorry

end QAlgorithms.Papers.Independent.Extend50.P32

end
