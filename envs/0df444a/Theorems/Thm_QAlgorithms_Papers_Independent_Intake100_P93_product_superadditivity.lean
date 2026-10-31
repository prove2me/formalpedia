-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P93_product_superadditivity
-- name    : QAlgorithms.Papers.Independent.Intake100.P93.product_superadditivity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:38:26.181727+00:00
-- url     : https://prove2.me/theorems/ef51f623-1a28-4124-abaa-1187f309c5cd
-- title:
--   §III: assistance is not additive for general tensor products
-- statement:
--   Let $\rho^B$ and $\sigma^{A'}$ be normalized finite-dimensional states that are not pure. Let $u\in A$ and $v\in B'$ be unit vectors in nonzero local spaces. Set $\rho^{AB}=|u\rangle\langle u|\otimes\rho^B$ and $\sigma^{A'B'}=\sigma^{A'}\otimes|v\rangle\langle v|$. For the one-copy entanglement of assistance,
--
--   $$E_A(\rho)=E_A(\sigma)=0,\qquad E_A(\rho\otimes\sigma)>0.$$
--
--   The product is viewed across $AA':BB'$. Strict mixing means failure to be pure, not full rank. Arbitrary local unit vectors express the source's choice of basis vector $|0\rangle$. This is a concrete nonadditivity statement for the ensemble roof.
-- source:
--   Entanglement of assistance and multipartite state distillation, arXiv:quant-ph/0505038v1, PDF p. 3, §III: assistance is not additive for general tensor products

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P93

namespace QAlgorithms.Papers.Independent.Intake100.P93

open scoped Matrix ComplexConjugate ComplexOrder

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted primitives; no chunk-local aliases.

open Information100.P21 (Op)

open Information100.P08 (PureEnsemble)

open Dependency50.P07 (bipartiteProduct)

open Information100.P67 (receiverChannel)

open Support50.P11 (choiState)

/-- PDF p.3, Section III: strictly mixed means not pure, without a full-rank
assumption. The product is regrouped across AA':BB'. -/
theorem product_superadditivity {a b a2 b2 : ℕ}
    (ha : 0 < a) (hb : 0 < b) (ha2 : 0 < a2) (hb2 : 0 < b2)
    (u : EuclideanSpace ℂ (Fin a)) (v : EuclideanSpace ℂ (Fin b2))
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (rhoB : Op (Fin b)) (sigmaA : Op (Fin a2))
    (hrho : IsDensityMatrix rhoB) (hsigma : IsDensityMatrix sigmaA)
    (hmrho : ¬ Information100.P08.IsPure rhoB)
    (hmsigma : ¬ Information100.P08.IsPure sigmaA) :
    let rho := Matrix.kronecker (pureDensity u) rhoB
    let sigma := Matrix.kronecker sigmaA (pureDensity v)
    assistance rho = 0 ∧ assistance sigma = 0 ∧
      0 < assistance (bipartiteProduct rho sigma) := by sorry

end

end QAlgorithms.Papers.Independent.Intake100.P93
