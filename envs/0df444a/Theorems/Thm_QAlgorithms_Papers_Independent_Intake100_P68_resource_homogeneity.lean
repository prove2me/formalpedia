-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P68_resource_homogeneity
-- name    : QAlgorithms.Papers.Independent.Intake100.P68.resource_homogeneity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T18:16:27.971274+00:00
-- url     : https://prove2.me/theorems/b6f26ea0-ec33-4f48-8f73-80c95d1e8e04
-- title:
--   Note [14], Eq.(37): homogeneity of asymptotic resource products
-- statement:
--   Let $E$ be a finite real-valued functional on finite bipartite asymptotic resource products. Assume only that an actual asymptotic LOCC conversion $R^{\otimes x}\to S^{\otimes y}$, with $x>0$ and $y\ge0$, implies $yE(S)\le xE(R)$. Supplies mean independent integer copy counts with floors; conversion permits every positive error and rate slack, all sufficiently large block lengths, and unconditional normalized output. The same functional is used across positive finite local dimensions. Neither additivity nor continuity is assumed.
--
--   Let $\rho_1,\rho_2$ be normalized densities on positive finite bipartite systems, and let $x,x_1,x_2,y\ge0$ be real supplies. Then
--
--   $$E(\rho_1^{\otimes x})=xE(\rho_1),$$
--
--   $$E(\rho_1^{\otimes yx_1}\otimes\rho_2^{\otimes yx_2})=yE(\rho_1^{\otimes x_1}\otimes\rho_2^{\otimes x_2}).$$
--
--   These are homogeneity identities for formal asymptotic resources whose integer supplies use floors. Homogeneity is a conclusion, not an axiom of the functional. Zero supplies are retained, and additivity of the two distinct species is not asserted.
--
--   This statement records the source result at fixed finite dimensions and can be reused with the same operational conversion convention.
-- source:
--   On the continuity of asymptotic measures of entanglement, arXiv:quant-ph/0203107v1, PDF p. 5, Note [14], Eq.(37): homogeneity of asymptotic resource products

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P68

noncomputable section

open Filter Topology

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intake100.P68

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (FiniteLOCC)

/-- PDF pp.4–5 [14], (37): real supply homogeneity derived from actual
rescaling conversions, not assumed in IsAsymptoticMeasure. Joint resource
values need not be sums of single-species values. Zero supplies are included. -/
theorem resource_homogeneity
    (E : SupplyProduct → ℝ) (hE : IsAsymptoticMeasure E)
    {a b c d : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (rho : VidalOperator a b) (sigma : VidalOperator c d)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (x x1 x2 y : ℝ) (hx : 0 ≤ x) (hx1 : 0 ≤ x1) (hx2 : 0 ≤ x2) (hy : 0 ≤ y) :
    E (single rho x) = x * resourceSingleValue E rho ∧
      E (single rho (y*x1) ++ single sigma (y*x2)) =
        y * E (single rho x1 ++ single sigma x2) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P68

end
