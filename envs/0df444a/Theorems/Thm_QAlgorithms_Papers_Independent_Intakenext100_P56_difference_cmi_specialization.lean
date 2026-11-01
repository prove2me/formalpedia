-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P56_difference_cmi_specialization
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P56.difference_cmi_specialization
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:02:08.580032+00:00
-- url     : https://prove2.me/theorems/0cb2a36d-98a7-408f-9152-244f545bd4e7
-- title:
--   Unnumbered: conditional-information specialization (6.16)–(6.18)
-- statement:
--   All systems are finite-dimensional complex Hilbert spaces with nonempty finite bases. States are positive semidefinite operators of trace one; pure kets have norm one. All marginal states below are partial traces of the stated joint state. Logarithms are natural, and spectral powers vanish on the kernel, including at exponent zero.
--
--   For any tripartite density $\rho_{ABC}$ and $\alpha>0$, $\alpha\ne1$, let $\sigma=\rho_B\otimes\rho_{AC}$ in ABC ordering and let $\mathcal N=\operatorname{Tr}_A$. Then
--
--   $$\Delta_\alpha(\rho,\sigma,\mathcal N)=I^{\rm fixed}_\alpha(A;B|C)_\rho,\qquad\widetilde\Delta_\alpha(\rho,\sigma,\mathcal N)=\widetilde I^{\rm fixed}_\alpha(A;B|C)_\rho.$$
--
--   The right sides are exactly (6.17) and (6.18), with both computed support factors $\rho_B^0$, not the optimized Petz CMI of (3.18). Every factor is embedded in the same ABC space. Generalized powers allow singular inputs; no singular-input limit theorem is asserted. This is the claimed algebraic specialization. The fixed-reference sandwiched expression is also identified with the sandwiched CMI (5.42).
-- source:
--   Rényi squashed entanglement, discord, and relative entropy differences, arXiv:1410.1443v3, PDF p. 25, Unnumbered: conditional-information specialization (6.16)–(6.18)

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

/-- arXiv:1410.1443v3, PDF p.25, (6.16)–(6.18): fixed-reference
specialization, including generalized powers on singular inputs.
No identity with optimized (3.18) and no singular-input limit is asserted. -/
theorem difference_cmi_specialization (a : ℝ) (ha : RenyiOrder a)
    (rho : Op (A × (B × C))) (hrho : IsDensityMatrix rho) :
    differencePetz a rho (cmiReference rho) traceLeft = fixedPetzCMI a rho ∧
    differenceSandwiched a rho (cmiReference rho) traceLeft = fixedSandwichedCMI a rho ∧
    fixedSandwichedCMI a rho = sandwichedCMI a rho := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P56

end
