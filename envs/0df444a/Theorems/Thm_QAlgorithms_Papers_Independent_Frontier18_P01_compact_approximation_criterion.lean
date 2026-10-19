-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P01_compact_approximation_criterion
-- name    : QAlgorithms.Papers.Independent.Frontier18.P01.compact_approximation_criterion
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:55:47.634477+00:00
-- url     : https://prove2.me/theorems/d216aee1-3ac0-4eb3-acc6-3b10311fc663
-- title:
--   Equation (29): compact-uniform approximation criterion for continuity
-- statement:
--   All Hilbert spaces are complex and separable, with completed Hilbert tensor products. States are positive trace-class operators of trace one, and channels are completely positive and trace preserving. Write $H$ for entropy and $D$ for relative entropy, using natural logarithms; $I(\rho,\Phi)$ is the relative entropy of the channel-applied purification against the product of its marginals. Fix $\Phi$ and a subset $A$ of input states. For $k\ge1$, let $I_k(\rho,\Phi)$ be the supremum of $\sum_i p_iI(\rho_i,\Phi)$ over countable ensembles with barycenter $\rho$ and constituent ranks at most $k$. Then $I(\cdot,\Phi)$ is finite-valued and continuous on $A$ if and only if
--
--   $$\forall C\subseteq A\text{ compact},\ \forall\varepsilon>0,\ \exists K\ge1,\ \forall k\ge K,\ \forall\rho\in C:\ I(\rho,\Phi)\le I_k(\rho,\Phi)+\varepsilon,$$
--
--   with finite $I$ on each such $C$. Empty compact sets impose no condition. This is exactly compact-uniform vanishing of the approximation deficit, not uniform convergence on all of $A$.
-- source:
--   Mutual and coherent informations for infinite-dimensional quantum channels, arXiv:1004.2495v2, PDF p. 20, Equation (29): compact-uniform approximation criterion for continuity

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P01

noncomputable section

open Filter

open scoped ENNReal

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Frontier18.P01

variable {I J K L E R : Type}

/-- Equation (29), PDF pp.20–21. Finite-valued continuity iff epsilon-uniform
approximation on EACH compact subset. Empty compact subsets are harmless. -/
theorem compact_approximation_criterion [Countable I] [Countable J] (Phi : Channel I J) (A : Set (State I)) :
    ((∀ rho ∈ A, mutualInformation rho.coefficients Phi.val < ⊤) ∧
      ContinuousOn (fun rho : State I => (mutualInformation rho.coefficients Phi.val).toReal) A) ↔
    ∀ C : Set (State I), C ⊆ A → IsCompact C →
      UniformApprox C (fun rho => mutualInformation rho.coefficients Phi.val)
        (fun k rho => mutualApprox k rho.coefficients Phi.val) := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P01

end
