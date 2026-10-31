-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P47_pinching_penalty
-- name    : QAlgorithms.Papers.Independent.Intake100.P47.pinching_penalty
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:24:28.522986+00:00
-- url     : https://prove2.me/theorems/6d8bfe3e-95fd-45b3-aeb0-4e9d2e669aa9
-- title:
--   Lemma 3: Two-sided pinching penalty
-- statement:
--   All Hilbert spaces are finite dimensional and nonzero. States are positive semidefinite operators of trace one, logarithms are natural, and $\rho\ll\sigma$ means inclusion of supports. Write $D_\alpha$ and $\widetilde D_\alpha$ for the Petz and sandwiched divergences, respectively, with generalized inverse powers on support and orders $0,1,\infty$ defined by limits. Let $\rho$ be a state, $\sigma\ge0$, and $\mathcal P_\sigma$ its spectral pinching. Let $v_\sigma$ count its distinct eigenvalues, including zero. For all orders $\alpha\ge0$, including the limiting orders,
--   $$\widetilde D_\alpha(\mathcal P_\sigma(\rho)\|\sigma)\le\widetilde D_\alpha(\rho\|\sigma)\le\widetilde D_\alpha(\mathcal P_\sigma(\rho)\|\sigma)+c_\alpha\log v_\sigma,$$
--   where $c_\alpha=1$ for $0\le\alpha\le2$ and $c_\alpha=2$ for $\alpha>2$. This bounds the loss caused by pinching in extended-real form, including support failure.
-- source:
--   Correlation Detection and an Operational Interpretation of the Renyi Mutual Information, arXiv:1408.6894v5, PDF p. 7, Lemma 3: Two-sided pinching penalty

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P47

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P47

open scoped BigOperators Matrix ComplexOrder ComplexConjugate Topology

open Filter QAlgorithms

open QAlgorithms.Papers.Independent.Information100.P22 (Op mixed)

open QAlgorithms.Papers.Independent.Information100.P60 (copies)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms.Papers.Independent.Dependency50.P28 (SupportLE pinch logNonnegativeExtended)

open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy IsSupported)

open QAlgorithms.Papers.Independent.Bridge50.P49 (groupedProduct)

open QAlgorithms.Papers.Independent.Claimed50.P12 (DiagonalIn)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C D I J : Type}

variable [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype I] [Fintype J]

variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

variable [DecidableEq I] [DecidableEq J]

/-- arXiv:1408.6894v5, PDF p.7, Lemma 3, BOTH inequalities of (2.18).
Includes orders 0,1,infinity and counts distinct eigenvalues including zero. -/
theorem pinching_penalty [Nonempty I] (rho sigma : Op I)
    (hr : IsDensityMatrix rho) (hs : sigma.PosSemidef) (a : RenyiOrder) (ha : 0 ≤ a) :
    completedRenyiDivergence true a (pinch sigma rho) sigma ≤ completedRenyiDivergence true a rho sigma ∧
    completedRenyiDivergence true a rho sigma ≤ completedRenyiDivergence true a (pinch sigma rho) sigma +
      (((if a ≤ 2 then 1 else 2 : ℝ) * Real.log (spectrumCount sigma) : ℝ) : EReal) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P47

end
