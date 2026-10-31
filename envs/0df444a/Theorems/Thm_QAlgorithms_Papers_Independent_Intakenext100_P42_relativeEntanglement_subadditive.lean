-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P42_relativeEntanglement_subadditive
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P42.relativeEntanglement_subadditive
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:52:34.752183+00:00
-- url     : https://prove2.me/theorems/2cef300a-21bf-446b-92b8-374dedf6945d
-- title:
--   Unnumbered Eq.(76): subadditivity
-- statement:
--   All local registers are nonzero and finite-dimensional. Density matrices are positive semidefinite with trace one. Entropies use natural logarithms, $0\ln0=0$, and Umegaki relative entropy $S(\sigma\Vert\rho)$ is $+\infty$ on failure of support inclusion. The relative entropy of entanglement is $E_R(\sigma)=\inf_{\rho\in\mathrm{Sep}}S(\sigma\Vert\rho)$, where separability is across the specified Alice:Bob cut.
--
--   Let $\sigma_{12}$ and $\tau_{34}$ be density matrices on arbitrary nonzero finite local registers. Alice holds 1 and 3 and Bob holds 2 and 4. Then
--
--   $$E_R^{13:24}(\sigma_{12}\otimes\tau_{34})\le E_R^{1:2}(\sigma_{12})+E_R^{3:4}(\tau_{34}).$$
--
--   The left minimization permits arbitrary entanglement inside either party’s registers. This subadditivity is separate from conjectured equality.
-- source:
--   Entanglement Measures and Purification Procedures, arXiv:quant-ph/9707035v2, PDF p. 26, Unnumbered Eq.(76): subadditivity

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P42

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal Topology

namespace QAlgorithms.Papers.Independent.Intakenext100.P42

open QAlgorithms QAlgorithms.Entanglement

open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P04 (copies)

open QAlgorithms.Papers.Independent.Bridge50.P49 (groupedProduct)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.26, Eq.(76): subadditivity across Alice's combined registers versus Bob's.
The comparison set permits arbitrary entanglement inside either party's registers. -/
theorem relativeEntanglement_subadditive {I J A B : Type}
    [Fintype I] [Fintype J] [Fintype A] [Fintype B]
    [DecidableEq I] [DecidableEq J] [DecidableEq A] [DecidableEq B]
    [Nonempty I] [Nonempty J] [Nonempty A] [Nonempty B]
    (sigma : Matrix (I × J) (I × J) ℂ) (tau : Matrix (A × B) (A × B) ℂ)
    (hsigma : IsDensityMatrix sigma) (htau : IsDensityMatrix tau) :
    relativeEntanglementNats (groupedProduct sigma tau) ≤
      relativeEntanglementNats sigma + relativeEntanglementNats tau := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P42

end
