-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P16_concrete_sdp_representation
-- name    : QAlgorithms.Papers.Independent.Extend50.P16.concrete_sdp_representation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:04:33.316495+00:00
-- url     : https://prove2.me/theorems/ce98ee7e-c5bc-4425-9cee-6409f998c30b
-- title:
--   Concrete finite-dimensional SDP for kappa-entanglement
-- statement:
--   Let $\rho_{AB}$ be a positive semidefinite trace-one operator on nonzero finite-dimensional complex spaces with fixed product bases. Let $T_B$ denote transpose on the second factor. Construct $D=I$, $\Psi(S)=\operatorname{diag}(T_B(S),T_B(S))$, and $C_\rho=\operatorname{diag}(T_B(\rho),-T_B(\rho))$. If
--
--   $$
--   s_\rho=\inf\{\operatorname{Tr}(DS):S\succeq0,\ \Psi(S)\succeq C_\rho\},
--   \qquad\text{then}\qquad E_\kappa(\rho)=\log_2 s_\rho.
--   $$
--
--   Here $E_\kappa$ is independently defined as the infimum of $\log_2\operatorname{Tr}S$ over $S\succeq0$ satisfying $-T_B(S)\preceq T_B(\rho)\preceq T_B(S)$. The formula gives an actual SDP representation with all matrices constructed from the input, without asserting a numerical runtime.
-- source:
--   Cost of quantum entanglement simplified, arXiv:2007.14270v1, PDF p. 13, Unnumbered main result: concrete finite-dimensional SDP, B.2 Eq.(S12)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P16

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P16

open QAlgorithms Filter

open QAlgorithms.Papers.Independent.Dependency50.P32 (partialTranspose)

open QAlgorithms.Papers.Independent.Dependency50.P41 (maximallyEntangled)

open QAlgorithms.Papers.Independent.Information100.P80 (groupedPower)

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.13, (S12), with the constructed standard form on p.15, (S16):
κ is the base-two logarithm of the value of the concrete finite SDP. -/
theorem concrete_sdp_representation {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (rho : BipMat A B) (hrho : IsDensityMatrix rho) :
    kappaEntanglement rho = extendedLogTwo (kappaSdpValue rho) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P16

end
