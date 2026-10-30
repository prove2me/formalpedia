-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P29_typicalSubspaceMass
-- name    : QAlgorithms.Papers.Independent.Advance50.P29.typicalSubspaceMass
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:15:46.733141+00:00
-- url     : https://prove2.me/theorems/990f22fd-5b06-4a80-b596-ed523c20d3eb
-- title:
--   §7.2 (ii-prime): exponentially high typical-subspace mass
-- statement:
--   Let $Q$ and $Q^{\prime}$ be finite complex Hilbert spaces of positive dimensions $M$ and $D$. A density operator is positive semidefinite with trace one. All logarithms and entropies are in bits. Write $\pi=I_Q/M$. Let $\rho$ be a density operator and $\varepsilon>0$. Let $T_{\varepsilon,n}$ be the span of all eigenvectors of $\rho^{\otimes n}$ whose eigenvalues lie in the closed interval $[2^{-n(S(\rho)+\varepsilon)},2^{-n(S(\rho)-\varepsilon)}]$, and let $\Pi_{\varepsilon,n}$ be its orthogonal projector. There exists $\psi>0$, depending on $\rho$ and $\varepsilon$ but independent of $n$, such that every positive integer $n$ obeys
--
--   $$
--   \operatorname{tr}(\Pi_{\varepsilon,n}\rho^{\otimes n})>1-2e^{-n\psi}.
--   $$
--
--   A normalized density is almost entirely supported on its weakly typical spectral subspace.
-- source:
--   A random-coding based proof for the quantum coding theorem, arXiv:0712.2558v1, PDF p. 16, §7.2 (ii-prime): exponentially high typical-subspace mass

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P29

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P29

open QAlgorithms MeasureTheory Filter

open QAlgorithms.Papers.Independent.Information100.P22
  (densityPurification coherentInformation singleUseInformation mixed)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

open QAlgorithms.Papers.Independent.Dependency50.P48 (wordProbability)

open QAlgorithms.Papers.Independent.Bridge50.P43 (tensorDensity)

open scoped Matrix ComplexConjugate ComplexOrder Topology

attribute [local instance] Classical.propDecidable

variable {I J E L : Type} [Fintype I] [DecidableEq I]

variable [Fintype J] [DecidableEq J] [Fintype E] [DecidableEq E]

variable [Fintype L] [DecidableEq L]

/-- PDF p.16, §7.2(ii'): exponentially high mass of the full closed-window spectral subspace. -/
theorem typicalSubspaceMass [Nonempty I] (rho : Matrix I I ℂ)
    (hrho : IsDensityMatrix rho) (epsilon : ℝ) (he : 0 < epsilon) :
    ∃ psi : ℝ, 0 < psi ∧ ∀ n : ℕ, 0 < n →
      1 - 2 * Real.exp (-(n : ℝ) * psi) <
        (weakTypicalProjector rho epsilon n * tensorDensity rho n).trace.re := by sorry

end QAlgorithms.Papers.Independent.Advance50.P29

end
