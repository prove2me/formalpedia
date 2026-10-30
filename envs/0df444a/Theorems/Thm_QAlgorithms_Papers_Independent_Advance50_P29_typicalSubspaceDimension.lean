-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P29_typicalSubspaceDimension
-- name    : QAlgorithms.Papers.Independent.Advance50.P29.typicalSubspaceDimension
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:14:44.257089+00:00
-- url     : https://prove2.me/theorems/72d0d995-9a5c-4163-ba82-4b302b48c87b
-- title:
--   §7.2 (i-prime): weakly typical subspace dimension
-- statement:
--   Let $Q$ and $Q^{\prime}$ be finite complex Hilbert spaces of positive dimensions $M$ and $D$. A density operator is positive semidefinite with trace one. All logarithms and entropies are in bits. Write $\pi=I_Q/M$. Let $\rho$ be a density operator and $\varepsilon>0$. Let $T_{\varepsilon,n}$ be the span of all eigenvectors of $\rho^{\otimes n}$ whose eigenvalues lie in the closed interval $[2^{-n(S(\rho)+\varepsilon)},2^{-n(S(\rho)-\varepsilon)}]$, and let $\Pi_{\varepsilon,n}$ be its orthogonal projector. For every positive integer $n$,
--
--   $$
--   \dim T_{\varepsilon,n}<2^{n(S(\rho)+\varepsilon)}.
--   $$
--
--   The spectral typical subspace has controlled dimension. **Formalization Note** The dimension is represented by the real trace of its orthogonal projector.
-- source:
--   A random-coding based proof for the quantum coding theorem, arXiv:0712.2558v1, PDF p. 15, §7.2 (i-prime): weakly typical subspace dimension

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

/-- PDF pp.15–16, §7.2(i'): trace of the spectral projection is the typical-subspace dimension. -/
theorem typicalSubspaceDimension [Nonempty I] (rho : Matrix I I ℂ)
    (hrho : IsDensityMatrix rho) (epsilon : ℝ) (he : 0 < epsilon)
    (n : ℕ) (hn : 0 < n) :
    (weakTypicalProjector rho epsilon n).trace.re <
      (2 : ℝ) ^ ((n : ℝ) * (vnEntropy rho + epsilon)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P29

end
