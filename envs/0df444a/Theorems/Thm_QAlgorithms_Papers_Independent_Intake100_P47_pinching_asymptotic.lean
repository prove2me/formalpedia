-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P47_pinching_asymptotic
-- name    : QAlgorithms.Papers.Independent.Intake100.P47.pinching_asymptotic
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:25:17.523637+00:00
-- url     : https://prove2.me/theorems/c43a0d29-e053-4844-9ee4-21bf79cda315
-- title:
--   Corollary 4: Asymptotic pinching achieves sandwiched divergence
-- statement:
--   All Hilbert spaces are finite dimensional and nonzero. States are positive semidefinite operators of trace one, logarithms are natural, and $\rho\ll\sigma$ means inclusion of supports. Write $D_\alpha$ and $\widetilde D_\alpha$ for the Petz and sandwiched divergences, respectively, with generalized inverse powers on support and orders $0,1,\infty$ defined by limits. For a state $\rho$, any positive semidefinite $\sigma$, and every order $\alpha\ge0$ (including limiting orders),
--   $$\lim_{n\to\infty}\frac1nD_\alpha\bigl(\mathcal P_{\sigma^{\otimes n}}(\rho^{\otimes n})\|\sigma^{\otimes n}\bigr)=\widetilde D_\alpha(\rho\|\sigma).$$
--   The left divergence is Petz; the right divergence is sandwiched. The limit is in the extended real line, so no support assumption is needed. This gives an asymptotic classical realization of the sandwiched divergence.
-- source:
--   Correlation Detection and an Operational Interpretation of the Renyi Mutual Information, arXiv:1408.6894v5, PDF p. 8, Corollary 4: Asymptotic pinching achieves sandwiched divergence

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

/-- arXiv:1408.6894v5, PDF p.8, Corollary 4, (2.29).
LEFT is Petz; RIGHT is sandwiched. No support inclusion is imposed. -/
theorem pinching_asymptotic [Nonempty I] (rho sigma : Op I)
    (hr : IsDensityMatrix rho) (hs : sigma.PosSemidef) (a : RenyiOrder) (ha : 0 ≤ a) :
    Tendsto (fun k : ℕ => (((((k+1 : ℕ) : ℝ)⁻¹ : ℝ) : EReal) *
      completedRenyiDivergence false a (pinch (copies (k+1) sigma) (copies (k+1) rho)) (copies (k+1) sigma)))
      atTop (𝓝 (completedRenyiDivergence true a rho sigma)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P47

end
