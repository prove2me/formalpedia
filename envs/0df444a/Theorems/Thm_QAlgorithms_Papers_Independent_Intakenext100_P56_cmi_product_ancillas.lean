-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P56_cmi_product_ancillas
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P56.cmi_product_ancillas
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:58:29.831687+00:00
-- url     : https://prove2.me/theorems/b19538a3-3619-4acc-b68d-8c6db8a9e3c4
-- title:
--   Lemma 30
-- statement:
--   All systems are finite-dimensional complex Hilbert spaces with nonempty finite bases. States are positive semidefinite operators of trace one; pure kets have norm one. All marginal states below are partial traces of the stated joint state. Logarithms are natural, and spectral powers vanish on the kernel, including at exponent zero.
--
--   Let $\omega_{ABC}$ be a state and let $\sigma_{A_1},\tau_{B_1},\gamma_{C_1}$ be arbitrary mixed ancillary states, independent of it and each other. Put $\rho=\omega\otimes\sigma\otimes\tau\otimes\gamma$, regrouped by party. For every positive order, with the ordinary continuous value at one,
--
--   $$I_\alpha(AA_1;BB_1|CC_1)_\rho=I_\alpha(A;B|C)_\omega.$$
--
--   The formula uses the actual partial traces of this product state. It expresses invariance under adjoining independent local and conditioning ancillas.
-- source:
--   Rényi squashed entanglement, discord, and relative entropy differences, arXiv:1410.1443v3, PDF p. 32, Lemma 30

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P56

noncomputable section

open Filter Topology

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intakenext100.P56

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw entropy average holevo)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms.Papers.Independent.Dependency50.P21 (channelAdjoint petz extendedLog marginalAB)

open QAlgorithms.Papers.Independent.Information100.P21 (Op FiniteLOCC)

open QAlgorithms.Papers.Independent.Dependency50.P35 (marginalAC)

open QAlgorithms.Papers.Independent.Dependency50.P07 (bipartiteProduct)

open QAlgorithms.Papers.Independent.Information100.P67 (squaredFidelity)

open QAlgorithms.Papers.Independent.Advance50.P25 (renyiEntropyNats)

variable {A B C D E X : Type}

variable [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype E] [Fintype X]

variable [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D] [Nonempty E] [Nonempty X]

open scoped Matrix.Norms.L2Operator

/-- arXiv:1410.1443v3, PDF pp.32–33, Lemma 30, (A.1).
The one endpoint is the ordinary CMI extension; all ancillas may be mixed. -/
theorem cmi_product_ancillas {A1 B1 C1 : Type}
    [Fintype A1] [Fintype B1] [Fintype C1]
    [Nonempty A1] [Nonempty B1] [Nonempty C1]
    (a : ℝ) (ha : 0 < a) (rho : Op (A × (B × C))) (hrho : IsDensityMatrix rho)
    (sigma : Op A1) (tau : Op B1) (gamma : Op C1)
    (hsigma : IsDensityMatrix sigma) (htau : IsDensityMatrix tau) (hgamma : IsDensityMatrix gamma) :
    renyiCMI a (addAncillas rho sigma tau gamma) = renyiCMI a rho := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P56

end
