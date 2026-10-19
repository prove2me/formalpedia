-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P01_bounded_rank_continuity
-- name    : QAlgorithms.Papers.Independent.Frontier18.P01.bounded_rank_continuity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:53:15.597718+00:00
-- url     : https://prove2.me/theorems/de1240c3-2110-4368-9933-afddbc4c1ce3
-- title:
--   Remark 3: bounded-rank input continuity and boundedness
-- statement:
--   All Hilbert spaces are complex and separable, with completed Hilbert tensor products. States are positive trace-class operators of trace one, and channels are completely positive and trace preserving. Write $H$ for entropy and $D$ for relative entropy, using natural logarithms; $I(\rho,\Phi)$ is the relative entropy of the channel-applied purification against the product of its marginals. For any channel $\Phi$ and positive integer $k$, define $S_k=\{\rho:\operatorname{rank}\rho\le k\}$. Then
--
--   $$\rho\longmapsto I(\rho,\Phi)\quad\text{is continuous and bounded on }S_k.$$
--
--   Boundedness means that a single finite constant bounds all values on this whole set. No common finite-dimensional support or compactness assumption is imposed. In particular, for $k=1$ every input is pure and its mutual information is zero.
-- source:
--   Mutual and coherent informations for infinite-dimensional quantum channels, arXiv:1004.2495v2, PDF p. 20, Remark 3: bounded-rank input continuity and boundedness

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P01

noncomputable section

open Filter

open scoped ENNReal

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Frontier18.P01

variable {I J K L E R : Type}

/-- Remark 3, PDF p.20: continuity and boundedness on the entire rank≤k set,
not a fixed finite-dimensional support. No compactness premise is introduced. -/
theorem bounded_rank_continuity [Countable I] [Countable J] (Phi : Channel I J) (k : ℕ) (hk : 1 ≤ k) :
    ContinuousOn (fun rho : State I => mutualInformation rho.coefficients Phi.val)
      {rho | RankAtMost rho.coefficients k} ∧
    ∃ M : ℝ, ∀ rho : State I, RankAtMost rho.coefficients k →
      mutualInformation rho.coefficients Phi.val ≤ ENNReal.ofReal M := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P01

end
