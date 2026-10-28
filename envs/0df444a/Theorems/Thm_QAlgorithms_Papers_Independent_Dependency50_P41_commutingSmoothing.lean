-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P41_commutingSmoothing
-- name    : QAlgorithms.Papers.Independent.Dependency50.P41.commutingSmoothing
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T16:56:51.392541+00:00
-- url     : https://prove2.me/theorems/296d3de6-335e-4658-840f-6ffe35ee2065
-- title:
--   Commuting restriction for trace-norm smoothing
-- statement:
--   All systems are finite-dimensional complex Hilbert spaces of positive dimension. Logarithms and entropies are in bits. Let $\rho_{AB}=\sum_k\rho_A^k\otimes|k\rangle\langle k|$ be a normalized quantum-classical state, with positive A-blocks and orthonormal labels. Let $\varepsilon>0$, and let $\mathcal B_{qc}^\varepsilon(\rho)$ consist of positive operators in the same classical basis at full trace-norm distance at most $\varepsilon$, without any trace bound. Then $$\inf_{\sigma\in\mathcal B_{qc}^\varepsilon(\rho)}H_0(A|B)_\sigma=\inf_{\substack{\sigma\in\mathcal B_{qc}^\varepsilon(\rho)\[\sigma,\rho]=0}}H_0(A|B)_\sigma.$$
--
--   Thus the corrected infimum smoothing can be restricted to commuting candidates; arbitrary quantum states are not assumed to commute.
-- source:
--   Entanglement Cost of Quantum Channels, arXiv:1108.5357v3, PDF p. 20, Lemma 28

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

/-- arXiv:1108.5357v3, PDF pp.20–21, Lemma 28.
Equality of infima uses the corrected Definition 4, with no trace restriction on smoothing. -/
theorem commutingSmoothing {A B : Type} {K : Type*} [Fintype A] [Fintype B] [Fintype K]
    [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]
    (v : K → EuclideanSpace ℂ B) (hv : Orthonormal ℂ v)
    (blocks : K → Op A) (hblocks : ∀ k, (blocks k).PosSemidef)
    (hstate : IsDensityMatrix (cqOperator v blocks))
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    smoothH0 (cqOperator v blocks) v epsilon =
      commutingSmoothH0 (cqOperator v blocks) v epsilon := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P41

end
