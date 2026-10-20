-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P41_classicalConditionalH0
-- name    : QAlgorithms.Papers.Independent.Dependency50.P41.classicalConditionalH0
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:47:10.753278+00:00
-- url     : https://prove2.me/theorems/43739e93-3b49-4390-8863-7205e0c5b210
-- title:
--   Alternative conditional entropy of a classical-block positive operator
-- statement:
--   All systems are finite-dimensional complex Hilbert spaces of positive dimension. Logarithms and entropies are in bits. Let $\rho_{AB}=\sum_{k\in K}\rho_A^k\otimes|k\rangle\langle k|$, where each $\rho_A^k$ is positive semidefinite and the label vectors are orthonormal. No trace normalization is assumed. Let $\rho^0$ denote its support projector and define $H_0(A|B)_\rho=\sup_{\sigma_B\in\mathcal S(B)}\log_2\operatorname{tr}[\rho^0(I_A\otimes\sigma_B)]$. Then $$H_0(A|B)_\rho=\sup_{k\in K}\log_2\operatorname{rank}(\rho_A^k).$$ For a nonempty finite label set the supremum is a maximum. The extended conventions are $\log_2 0=-\infty$ and $\sup\varnothing=-\infty$.
--
--   This evaluates the entropy on quantum-classical positive operators, including the zero operator.
-- source:
--   Entanglement Cost of Quantum Channels, arXiv:1108.5357v3, PDF p. 4, Lemma 3

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P41

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P41

open scoped ComplexConjugate Matrix ComplexOrder

open Filter

open QAlgorithms.Papers.Independent.Information100.P06 (supportProjection)

open QAlgorithms.Papers.Independent.Information100.P08 (PureEnsemble formation pureAverage)

open QAlgorithms.Papers.Independent.Information100.P21 (Op FiniteLOCC spinFlip concurrence)

open QAlgorithms.Papers.Independent.Information100.P67 (conditionalEntropy groupedPower)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arXiv:1108.5357v3, PDF pp.4–5, Lemma 3, (8).
The empty label family and the zero operator use extended log 0 = minus infinity. -/
theorem classicalConditionalH0 {A B : Type} {K : Type*} [Fintype A] [Fintype B] [Fintype K]
    [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]
    (v : K → EuclideanSpace ℂ B) (hv : Orthonormal ℂ v)
    (blocks : K → Op A) (hblocks : ∀ k, (blocks k).PosSemidef) :
    conditionalH0 (cqOperator v blocks) = ⨆ k, logRank (blocks k) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P41

end
