-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P33_qSquashed_monotonicity
-- name    : QAlgorithms.Papers.Independent.Claimed50.P33.qSquashed_monotonicity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:35:26.482983+00:00
-- url     : https://prove2.me/theorems/56fb5668-1311-4dfe-af77-2725e94a5d65
-- title:
--   §IV.B: convexity, FLAGS and LOCC monotonicity of both q versions
-- statement:
--   Fix $m\ge2$ and either $F=I_m$ or $F=S_m$. Let $E_F^q$ be the unrestricted extension infimum of the corresponding conditional information, in bits and without $1/2$. On all finite-dimensional normalized $m$-party states this functional is convex, invariant under local unitaries, satisfies the local orthogonal-flags identity, vanishes on fully separable states, and is monotone on average under LOCC:
--
--   $$\sum_j p_j E_F^q(\sigma_j)\le E_F^q(\rho).$$
--
--   Here $\{p_j,\sigma_j\}$ is the complete outcome ensemble of any finite adaptive LOCC protocol on $\rho$, permitting different local output dimensions, ancillary preparation and disposal. In particular, flags belong to an honest party and not to the squashing register. This establishes the entanglement-monotone properties used later.
-- source:
--   Squashed entanglement for multipartite states and entanglement measures based on the mixed convex roof, arXiv:0704.2236v3, PDF p. 5, §IV.B: convexity, FLAGS and LOCC monotonicity of both q versions

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P33

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P33

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Section IV.B, PDF pp.4–5,(31)–(37): convexity, FLAGS, LUI and average
LOCC monotonicity of both q versions, and zero on fully separable states. -/
theorem qSquashed_monotonicity (m : ℕ) (hm : 2 ≤ m) : ∀ kind : InformationKind,
    IsConvexFunctional (squashedFunctional false kind : FiniteState m → ℝ) ∧
    SatisfiesFlags (squashedFunctional false kind : FiniteState m → ℝ) ∧
    IsLocalUnitaryInvariant (squashedFunctional false kind : FiniteState m → ℝ) ∧
    IsAdaptiveLOCCMonotone (squashedFunctional false kind : FiniteState m → ℝ) ∧
    ∀ s : FiniteState m, IsMixedFullySeparable s → squashedFunctional false kind s = 0 := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P33

end
