-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P06_measureWeakMixing_iff_pairErgodic
-- name    : QAlgorithms.Papers.Independent.Gap48.P06.measureWeakMixing_iff_pairErgodic
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T21:07:07.642527+00:00
-- url     : https://prove2.me/theorems/e03999c6-9e58-449e-ad53-3594fdec93de
-- title:
--   Weak mixing and ergodicity of the diagonal pair action
-- statement:
--   Let an abstract group $G$ act by measurable measure-preserving transformations on a finite measure space $(X,\Sigma,\mu)$. The action is weakly mixing when the complex $L^2$ representation on $1^\perp$ contains no nonzero finite-dimensional invariant subspace. Then
--
--   $$\text{the action on }X\text{ is weakly mixing}\quad\Longleftrightarrow\quad\text{the diagonal action on }(X\times X,\Sigma\otimes\Sigma,\mu\otimes\mu)\text{ is ergodic}.$$
--
--   Here ergodicity means that every invariant $L^2$ function is almost everywhere constant. Because $\mu$ is finite, $1^\perp$ is precisely the subspace of functions of integral zero. The equivalence includes the zero measure without normalization. It relates the representation-theoretic and dynamical descriptions of weak mixing.
-- source:
--   Reflection Positive Stochastic Processes Indexed by Lie Groups, arXiv:1510.07445v3, PDF p. 43, Proposition 5.29

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P06

noncomputable section

open MeasureTheory ProbabilityTheory Filter

open scoped Topology ENNReal NNReal

namespace QAlgorithms.Papers.Independent.Gap48.P06

/-- Proposition 5.29, PDF p.43: weak mixing is equivalent to ergodicity of
the diagonal action on the actual product measure. Finiteness is inherited
from Definition 5.28; zero mass is included without normalization. -/
theorem measureWeakMixing_iff_pairErgodic
    {G X : Type*} [Group G] [MeasurableSpace X]
    (mu : Measure X) [IsFiniteMeasure mu] (a : G → X → X)
    (hone : ∀ x, a 1 x = x)
    (hmul : ∀ g h x, a (g * h) x = a g (a h x))
    (hpres : ∀ g, MeasurePreserving (a g) mu mu) :
    MeasureWeaklyMixing mu a hpres ↔ PairActionErgodic mu a hpres := by sorry

end QAlgorithms.Papers.Independent.Gap48.P06

end
