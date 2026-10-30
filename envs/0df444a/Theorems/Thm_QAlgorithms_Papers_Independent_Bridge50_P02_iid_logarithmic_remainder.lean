-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P02_iid_logarithmic_remainder
-- name    : QAlgorithms.Papers.Independent.Bridge50.P02.iid_logarithmic_remainder
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T11:45:20.400195+00:00
-- url     : https://prove2.me/theorems/a4e48038-ec6e-4e07-b5aa-586f904c9549
-- title:
--   Theorem 3: IID expansion with logarithmic remainder
-- statement:
--   Fix faithful density matrices $\rho,\sigma$ on a nonzero finite-dimensional complex Hilbert space and $\varepsilon\in(0,1)$. For each $n\ge1$ let $\beta_n(\varepsilon)$ optimize the type-II error over all joint effects on $\rho^{\otimes n}$ versus $\sigma^{\otimes n}$, with type-I error at most $\varepsilon$. With natural-log relative entropy $D$ and pair information variance $V$, there exist $C>0$ and an integer $N\ge2$, depending only on the fixed pair and $\varepsilon$, such that for every $n\ge N$,
--   $$\left|{-\log\beta_n(\varepsilon)}-nD(\rho\Vert\sigma)-\sqrt{nV(\rho\Vert\sigma)}\,\Phi^{-1}(\varepsilon)\right|\le C\log n.$$
--
--   Equal states and $V=0$ are included. This finite-dimensional IID theorem does not supply an infinite-dimensional Gaussian-state expansion.
-- source:
--   Second-order asymptotics for quantum hypothesis testing in settings beyond i.i.d. - quantum lattice systems and more, arXiv:1510.04682v4, PDF p. 16, Theorem 3

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P02

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Bridge50.P02

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P15
  (evaluate positiveMatrixRpow modularMatrix modularQuadratic resolventOverlap petzOverlap
    finiteRelativeEntropyNats)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

open QAlgorithms.Papers.Independent.Information100.P63 (Mat tensorPower testingBeta)

open QAlgorithms.Papers.Independent.Information100.P58 (normalQuantile)

variable {I : Type} [Fintype I] [DecidableEq I]

/-- Theorem 3, PDF p.16: finite-dimensional IID logarithmic remainder.
The constants precede the block length and may depend on the fixed pair and epsilon.
Equal densities and variance zero are included. -/
theorem iid_logarithmic_remainder [Nonempty I] (rho sigma : Mat I)
    (hrho : QAlgorithms.IsDensityMatrix rho) (hsigma : QAlgorithms.IsDensityMatrix sigma)
    (hfaithfulRho : rho.PosDef) (hfaithfulSigma : sigma.PosDef)
    (epsilon : ℝ) (hepsilon : 0 < epsilon ∧ epsilon < 1) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      |optimalTestingExponentNats (tensorPower n rho) (tensorPower n sigma) epsilon -
        ((n : ℝ) * finitePairRelativeEntropyNats rho sigma +
          Real.sqrt ((n : ℝ) * pairInformationVarianceNats rho sigma) * normalQuantile epsilon)| ≤
        C * Real.log n := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P02

end
