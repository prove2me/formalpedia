-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P33_restrictedSquashed_monotone
-- name    : QAlgorithms.Papers.Independent.Claimed50.P33.restrictedSquashed_monotone
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:48:50.861674+00:00
-- url     : https://prove2.me/theorems/d73a322c-175b-4a95-9e3f-ecbee44ec7d8
-- title:
--   §VI: separable and PPT extension restricted squashing monotones
-- statement:
--   Fix $m\ge2$ and let $F=I_m$ or $F=S_m$. Restrict the defining squashing infimum either to extensions separable across the joint-honest-system versus environment cut or to extensions having positive partial transpose across that cut. In either case allow every normalized extension and every positive finite environment dimension, without $1/2$. The resulting functional $E_F^{\mathcal R}$ is nonnegative, vanishes on fully separable honest states, is convex and locally unitary invariant, satisfies the local FLAGS identity, and obeys
--
--   $$\sum_j p_j E_F^{\mathcal R}(\sigma_j)\le E_F^{\mathcal R}(\rho)$$
--
--   for every finite adaptive LOCC outcome ensemble. The cut imposes no separability among the honest parties themselves. This states the two named extension-class constructions, without the source's unsupported arbitrary-convex-set generalization.
-- source:
--   Squashed entanglement for multipartite states and entanglement measures based on the mixed convex roof, arXiv:0704.2236v3, PDF p. 12, §VI: separable and PPT extension restricted squashing monotones

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P33

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P33

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Section VI, PDF p.12: the two NAMED extension classes give entanglement
measures for both I and S. No arbitrary-convex-family claim is added. -/
theorem restrictedSquashed_monotone (m : ℕ) (hm : 2 ≤ m) :
    ∀ (restriction : ExtensionRestriction) (kind : InformationKind),
    IsConvexFunctional (restrictedFunctional restriction kind : FiniteState m → ℝ) ∧
    SatisfiesFlags (restrictedFunctional restriction kind : FiniteState m → ℝ) ∧
    IsLocalUnitaryInvariant (restrictedFunctional restriction kind : FiniteState m → ℝ) ∧
    IsAdaptiveLOCCMonotone (restrictedFunctional restriction kind : FiniteState m → ℝ) ∧
    (∀ s : FiniteState m, 0 ≤ restrictedFunctional restriction kind s) ∧
    ∀ s : FiniteState m, IsMixedFullySeparable s → restrictedFunctional restriction kind s = 0 := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P33

end
