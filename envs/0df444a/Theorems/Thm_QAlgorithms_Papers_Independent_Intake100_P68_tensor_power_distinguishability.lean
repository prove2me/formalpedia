-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P68_tensor_power_distinguishability
-- name    : QAlgorithms.Papers.Independent.Intake100.P68.tensor_power_distinguishability
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T18:18:00.265581+00:00
-- url     : https://prove2.me/theorems/59293507-8f42-4283-92b0-5fc98ee6a624
-- title:
--   Note [10]: asymptotic distinguishability of distinct nearby tensor powers
-- statement:
--   Let $\rho\ne\sigma$ be normalized densities on the same positive finite bipartite local dimensions. Fix $0<\epsilon\le1$ and put $\rho_\epsilon=(1-\epsilon)\rho+\epsilon\sigma$. Then
--
--   $$\lim_{N\to\infty}T(\rho^{\otimes N},\rho_\epsilon^{\otimes N})=1.$$
--
--   The fixed distinctness and density-preserving range exclude the equal-state and invalid-mixture exceptions in the source's unqualified wording. The conclusion is asymptotically perfect distinguishability, without finite-block orthogonality or an exchange of regularization limits.
--
--   This statement records the source result at fixed finite dimensions and can be reused with the same operational conversion convention.
-- source:
--   On the continuity of asymptotic measures of entanglement, arXiv:quant-ph/0203107v1, PDF p. 4, Note [10]: asymptotic distinguishability of distinct nearby tensor powers

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P68

noncomputable section

open Filter Topology

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intake100.P68

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (FiniteLOCC)

/-- PDF p.4 [10]: distinct fixed perturbations of tensor powers become
asymptotically perfectly distinguishable. Printed: 'any epsilon>0', without
a distinctness exception. Changed: sigma != rho and 0<epsilon<=1.
Why: equal states have distance zero; the interval preserves density for
arbitrary rho,sigma and includes all sufficiently small positive perturbations.
The conclusion is the trace-distance limit, not finite-copy orthogonality. -/
theorem tensor_power_distinguishability
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (rho sigma : VidalOperator a b) (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (hne : sigma ≠ rho) (epsilon : ℝ) (hepsilon : 0 < epsilon) (hepsone : epsilon ≤ 1) :
    Tendsto (fun N : ℕ => traceDistance (ownedCopies rho N)
      (ownedCopies (affineMixture rho sigma epsilon) N)) atTop (nhds 1) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P68

end
