-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P01_deficit_relative_entropy
-- name    : QAlgorithms.Papers.Independent.Frontier18.P01.deficit_relative_entropy
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:56:24.967866+00:00
-- url     : https://prove2.me/theorems/333dbcb6-977c-4689-813a-80a5b7e07a85
-- title:
--   Section 6 unnumbered: relative-entropy formula for the approximation deficit
-- statement:
--   All Hilbert spaces are complex and separable, with completed Hilbert tensor products. States are positive trace-class operators of trace one, and channels are completely positive and trace preserving. Write $H$ for entropy and $D$ for relative entropy, using natural logarithms; $I(\rho,\Phi)$ is the relative entropy of the channel-applied purification against the product of its marginals. Let $\Phi,\widetilde\Phi$ be complementary, $H(\rho)<\infty$, and $k\ge1$. Let $\mathcal E_\rho^k$ contain countable ensembles with barycenter $\rho$ and constituent rank at most $k$, and define $I_k$ as the supremum of their average mutual information. Then
--
--   $$I(\rho,\Phi)-I_k(\rho,\Phi)=\inf_{\{p_i,\rho_i\}\in\mathcal E_\rho^k}\sum_{i:p_i>0}p_i\big[D(\rho_i\Vert\rho)+D(\Phi(\rho_i)\Vert\Phi(\rho))-D(\widetilde\Phi(\rho_i)\Vert\widetilde\Phi(\rho))\big].$$
--
--   Each positive-weight relative entropy is finite, and each bracket is nonnegative. The feasible ensembles exist by spectral decomposition, so the formula involves no undefined infinite differences.
-- source:
--   Mutual and coherent informations for infinite-dimensional quantum channels, arXiv:1004.2495v2, PDF p. 21, Section 6 unnumbered: relative-entropy formula for the approximation deficit

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P01

noncomputable section

open Filter

open scoped ENNReal

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Frontier18.P01

variable {I J K L E R : Type}

/-- Section 6 deficit formula, PDF p.21: input plus receiver minus complement.
Zero-weight terms are omitted before real differences are taken. -/
theorem deficit_relative_entropy [Countable I] [Countable J] [Countable E] (rho : State I) (Phi : Channel I J) (Psi : Channel I E)
    (hcomp : Complementary Phi Psi) (hin : homogeneousEntropy rho.coefficients < ⊤)
    (k : ℕ) (hk : 1 ≤ k) :
    deficit k rho.coefficients Phi.val =
      ⨅ e : RankedEnsemble rho.coefficients k,
        ensembleDeficit rho.coefficients Phi.val Psi.val e.val := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P01

end
