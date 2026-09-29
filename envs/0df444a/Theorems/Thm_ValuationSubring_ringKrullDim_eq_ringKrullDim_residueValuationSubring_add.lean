-- Prove2me | Theorems.Thm_ValuationSubring_ringKrullDim_eq_ringKrullDim_residueValuationSubring_add
-- name    : ValuationSubring.ringKrullDim_eq_ringKrullDim_residueValuationSubring_add
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/fe9b6499-a0c1-583a-ac28-43f20e2df5c6
-- title:
--   Additivity of Krull dimension for a pair of valuation subrings
-- statement:
--   Let $L$ be a field and let $A$ and $S$ be valuation subrings of $L$ with $A \le S$. From this data one forms the valuation subring `A.residueValuationSubring S h` of the residue field $\kappa(S)$ of the local ring $S$: it is the image of $A$ under the composite of the inclusion $A \hookrightarrow S$ with the residue map $S \to \kappa(S)$, this image being a valuation subring because for every $x \in \kappa(S)$ either $x$ or $x^{-1}$ lies in it. The theorem asserts the equality of Krull dimensions of commutative rings, taken in $\mathbb{N}\cup\{\infty\}$ with a bottom element adjoined and added there,
--   $$\operatorname{ringKrullDim} A = \operatorname{ringKrullDim}\bigl(\text{the residue valuation subring of } A \text{ in } \kappa(S)\bigr) + \operatorname{ringKrullDim} S.$$
--   Since the residue valuation subring is the image of $A$ modulo $\mathfrak{m}_S \cap A$, and $S$ is the localisation of $A$ at that prime, this is the classical additivity of the ranks of a valuation and of the two valuations into which it decomposes.
--
--   This is the rank formula for a composite valuation: the rank of $A$ is the sum of the rank of the induced valuation ring on the residue field of $S$ and the rank of $S$. It is used in the construction of good constant reductions in the development of [`AlgebraicCurve.exists_constantReduction_isGood_of_wittVector_normalFormOrder`](thm.html#AlgebraicCurve.exists_constantReduction_isGood_of_wittVector_normalFormOrder).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_ringKrullDim_eq_ringKrullDim_residueValuationSubring_add.lean

import Mathlib
import Definitions.Def_ValuationSubring_ResidueValuationSubring

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ValuationSubring.ringKrullDim_eq_ringKrullDim_residueValuationSubring_add
    {L : Type*} [Field L] (A S : ValuationSubring L) (h : A ≤ S) :
    ringKrullDim A = ringKrullDim (A.residueValuationSubring S h) + ringKrullDim S := by sorry
