-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P01_uniform_entropy_transfer
-- name    : QAlgorithms.Papers.Independent.Frontier18.P01.uniform_entropy_transfer
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:57:07.993989+00:00
-- url     : https://prove2.me/theorems/e4f41694-f1c5-4f69-a3aa-8c63c4d52956
-- title:
--   Equation (30): transfer of uniform entropy approximation to information
-- statement:
--   All Hilbert spaces are complex and separable, with completed Hilbert tensor products. States are positive trace-class operators of trace one, and channels are completely positive and trace preserving. Write $H$ for entropy and $D$ for relative entropy, using natural logarithms; $I(\rho,\Phi)$ is the relative entropy of the channel-applied purification against the product of its marginals. Fix any channel $\Phi$ and input-state subset $A$. Let $H_k(\rho)$ and $I_k(\rho,\Phi)$ be the suprema of average entropy and mutual information over ensembles with barycenter $\rho$ and constituent rank at most $k$. Then
--
--   $$H_k\longrightarrow H<\infty\text{ uniformly on }A\quad\Longrightarrow\quad I_k(\cdot,\Phi)\longrightarrow I(\cdot,\Phi)<\infty\text{ uniformly on }A.$$
--
--   Uniformity means: for every positive epsilon one index threshold works for every state in $A$, with finite target values. This transfers uniform entropy approximation to information approximation.
-- source:
--   Mutual and coherent informations for infinite-dimensional quantum channels, arXiv:1004.2495v2, PDF p. 21, Equation (30): transfer of uniform entropy approximation to information

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P01

noncomputable section

open Filter

open scoped ENNReal

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Frontier18.P01

variable {I J K L E R : Type}

/-- Equation (30), PDF p.21: UNIFORM convergence on all of A, not pointwise. -/
theorem uniform_entropy_transfer [Countable I] [Countable J] (Phi : Channel I J) (A : Set (State I))
    (h : UniformApprox A (fun rho => homogeneousEntropy rho.coefficients)
      (fun k rho => entropyApprox k rho.coefficients)) :
    UniformApprox A (fun rho => mutualInformation rho.coefficients Phi.val)
      (fun k rho => mutualApprox k rho.coefficients Phi.val) := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P01

end
