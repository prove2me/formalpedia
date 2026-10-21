-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P33_mixedRoof_LOCCMonotone
-- name    : QAlgorithms.Papers.Independent.Claimed50.P33.mixedRoof_LOCCMonotone
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:41:39.219887+00:00
-- url     : https://prove2.me/theorems/6ac903ba-60e9-4740-be74-b7db3758c322
-- title:
--   Theorem 1: mixed convex roofs are LOCC monotones
-- statement:
--   Fix $m\ge2$. Let $g$ be a real-valued functional on normalized states in all finite nonzero local dimensions. Assume it is continuous on each fixed finite state space and monotone on average under every local instrument, including dimension-changing operations and disposal. Its mixed convex roof is
--
--   $$E_g(\rho)=\inf_{\rho=\sum_i p_i\rho_i}\sum_i p_i g(\rho_i),$$
--
--   where all finite decompositions into mixed density matrices are allowed. Then $E_g$ is monotone on average under adaptive LOCC:
--
--   $$\sum_j q_j E_g(\sigma_j)\le E_g(\rho).$$
--
--   No nonnegativity or separable-state normalization of $g$ is imposed. This is a construction principle for mixed-roof monotones.
-- source:
--   Squashed entanglement for multipartite states and entanglement measures based on the mixed convex roof, arXiv:0704.2236v3, PDF p. 6, Theorem 1: mixed convex roofs are LOCC monotones

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P33

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P33

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Theorem 1, PDF pp.6–7: continuity and average LOCAL monotonicity imply
LOCC monotonicity of the MIXED convex roof. Arbitrary real g is allowed;
g=-1 is not excluded or incorrectly forced to vanish on separable states. -/
theorem mixedRoof_LOCCMonotone {m : ℕ} (hm : 2 ≤ m) (g : FiniteState m → ℝ)
    (hcont : IsContinuousFunctional g) (hlocal : IsAverageLocalMonotone g) :
    IsAdaptiveLOCCMonotone (bundledMixedRoof g) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P33

end
