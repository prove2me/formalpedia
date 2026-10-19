-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P01_joint_kraus_continuity
-- name    : QAlgorithms.Papers.Independent.Frontier18.P01.joint_kraus_continuity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:58:58.563834+00:00
-- url     : https://prove2.me/theorems/8bd35cc3-983a-4fd0-b259-dcf0481c63e6
-- title:
--   Corollary 2: joint continuity in state and countable Kraus family
-- statement:
--   All Hilbert spaces are complex and separable, with completed Hilbert tensor products. States are positive trace-class operators of trace one, and channels are completely positive and trace preserving. Write $H$ for entropy and $D$ for relative entropy, using natural logarithms; $I(\rho,\Phi)$ is the relative entropy of the channel-applied purification against the product of its marginals. Let $A$ be an input-state subset on which entropy is finite and real-valued continuous. Let $\mathcal V_1(A,B)$ be the countable Kraus families $V=(V_i)$ satisfying $\sum_iV_i^*V_i=\mathbf1$ strongly, endowed with coordinatewise strong operator topology. Write $\Phi[V](X)=\sum_iV_iXV_i^*$. All three functions
--
--   $$(\rho,V)\mapsto I(\rho,\Phi[V]),\qquad (\rho,V)\mapsto I_c(\rho,\Phi[V]),\qquad (\rho,V)\mapsto\sum_iH(V_i\rho V_i^*)$$
--
--   are continuous on $A\times\mathcal V_1(A,B)$. The third function uses homogeneous entropy. This includes measurement continuity without requiring convergence of Kraus adjoints.
-- source:
--   Mutual and coherent informations for infinite-dimensional quantum channels, arXiv:1004.2495v2, PDF p. 23, Corollary 2: joint continuity in state and countable Kraus family

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P01

noncomputable section

open Filter

open scoped ENNReal

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Frontier18.P01

variable {I J K L E R : Type}

/-- Corollary 2, PDF pp.22–24 (statement on p.23). All THREE functions are
jointly continuous for coordinatewise strong convergence of the Kraus family. -/
theorem joint_kraus_continuity [Countable I] [Countable J] (A : Set (State I))
    (hfinite : ∀ rho ∈ A, homogeneousEntropy rho.coefficients < ⊤)
    (hcont : ContinuousOn (fun rho : State I => (homogeneousEntropy rho.coefficients).toReal) A) :
    ContinuousOn (fun p : State I × KrausFamily I J => mutualInformation p.1.coefficients (countableKrausAction p.2))
      (A ×ˢ Set.univ) ∧
    ContinuousOn (fun p : State I × KrausFamily I J => finiteInputCoherentInfo p.1.coefficients (countableKrausAction p.2))
      (A ×ˢ Set.univ) ∧
    ContinuousOn (fun p : State I × KrausFamily I J => posteriorEntropy p.1.coefficients p.2)
      (A ×ˢ Set.univ) := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P01

end
