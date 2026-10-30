-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P29_uniformEntropies
-- name    : QAlgorithms.Papers.Independent.Advance50.P29.uniformEntropies
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:10:15.293757+00:00
-- url     : https://prove2.me/theorems/a0022c08-2dd2-4a46-beec-9186427f0363
-- title:
--   §6: uniform-channel exchange entropy and coherent information
-- statement:
--   Let $Q$ and $Q^{\prime}$ be finite complex Hilbert spaces of positive dimensions $M$ and $D$. A density operator is positive semidefinite with trace one. All logarithms and entropies are in bits. Write $\pi=I_Q/M$. For a state $\rho$, put $I(\rho,\mathcal N)=S(\mathcal N(\rho))-S_e(\rho,\mathcal N)$, where $S$ is von Neumann entropy and $S_e$ is the entropy of the reference/output state after applying $\mathcal N$ to a purification of $\rho$. Let $\mathcal U$ be CPTP and normalized-unital, meaning $\mathcal U(I_Q/M)=I_{Q^{\prime}}/D$. Assume it has a minimal Kraus family $(A_i)_{i=1}^r$ with $\operatorname{tr}(A_i^\dagger A_j)=0$ for $i\ne j$ and $M^{-1}\operatorname{tr}(A_i^\dagger A_i)=1/r$ for every $i$. Then
--
--   $$
--   S_e(\pi,\mathcal U)=\log_2r,\qquad S(\mathcal U(\pi))=\log_2D,\qquad I(\pi,\mathcal U)=\log_2D-\log_2r.
--   $$
--
--   The uniform Kraus weights identify the two entropies entering coherent information.
-- source:
--   A random-coding based proof for the quantum coding theorem, arXiv:0712.2558v1, PDF p. 14, §6: uniform-channel exchange entropy and coherent information

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

/-- PDF p.14, §6: uniform, normalized-unital channels have the stated exchange/output
entropies and coherent information; orthogonality alone is not uniformity. -/
theorem uniformEntropies [Nonempty I] [Nonempty J] [Nonempty L]
    (A : L → Matrix J I ℂ) (hA : IsKrausFamily A) (hu : UniformKraus A)
    (huni : NormalizedUnital (krausApply A)) :
    exchangeEntropy (krausApply A) (mixed I) = Real.logb 2 (Fintype.card L : ℝ) ∧
    vnEntropy (krausApply A (mixed I)) = Real.logb 2 (Fintype.card J : ℝ) ∧
    coherentInformation (krausApply A) (mixed I) =
      Real.logb 2 (Fintype.card J : ℝ) - Real.logb 2 (Fintype.card L : ℝ) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P29

end
