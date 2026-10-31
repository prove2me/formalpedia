-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P46_ree_border
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P46.ree_border
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:58:24.255574+00:00
-- url     : https://prove2.me/theorems/92bd0d1e-4935-4678-89b8-143b5cad67ec
-- title:
--   Theorem 1: unrestricted REE border minimizer
-- statement:
--   Let $\rho$ be an entangled density operator on a bipartite separable complex Hilbert space, with each component of dimension at least two. Finite and infinite dimensions are both allowed. Let $\mathcal S$ be the trace-norm closed convex hull of product densities, and let $D$ be extended Umegaki relative entropy in nats. There is a state $\sigma\in\mathcal S$ on the boundary of $\mathcal S$ relative to normalized states such that
--   $$D(\rho\Vert\sigma)=E_R(\rho):=\inf_{\tau\in\mathcal S}D(\rho\Vert\tau).$$
--   In infinite dimensions this boundary may be the entire separable set; the attainment clause remains substantive. The result has no Gaussian or energy restriction.
-- source:
--   Gaussian relative entropy of entanglement, arXiv:quant-ph/0402109v3, PDF p. 4, Theorem 1: unrestricted REE border minimizer

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P46

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P46

open scoped BigOperators ENNReal ComplexOrder Matrix

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsSeparable)

open QAlgorithms.Papers.Independent.Dependency50.P13
  (finiteRelativeEntropy compression entropyWeight)

open QAlgorithms.Papers.Independent.Claimed50.P47
  (Occupation bipartiteCharacteristic bipartiteWeyl gaussianStateCharacteristic)

-- These accepted definitions have the same completed Hilbert-space meaning.

open QAlgorithms.Papers.Independent.Next46.P13 (coordinateBasis)

open QAlgorithms.Papers.Independent.Frontier18.P18 (operatorCoeff boundedOperator)

open QAlgorithms.Papers.Independent.Claimed50.P41 (IsDiagonal)

/-- Chen, Theorem 1, PDF p.4: an entangled state has an attaining separable
minimizer on the relative trace-norm boundary of normalized states. In infinite
dimensions the boundary can equal the whole separable set; attainment remains. -/
theorem ree_border {I J : Type} [Countable I] [Countable J]
    [Nontrivial I] [Nontrivial J] (rho : State (I × J))
    (hentangled : ¬ IsSeparable rho.coefficients) :
    ∃ sigma : State (I × J), IsSeparable sigma.coefficients ∧
      StateBorder sigma ∧ operatorRelativeEntropy rho sigma = ree rho := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P46

end
