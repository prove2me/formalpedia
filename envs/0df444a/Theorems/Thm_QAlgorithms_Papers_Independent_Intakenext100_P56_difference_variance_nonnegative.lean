-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P56_difference_variance_nonnegative
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P56.difference_variance_nonnegative
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:03:32.333692+00:00
-- url     : https://prove2.me/theorems/eb9696ac-1436-4a4c-8e04-8f517942ad71
-- title:
--   Unnumbered: non-negativity of relative-entropy-difference variance
-- statement:
--   All systems are finite-dimensional complex Hilbert spaces with nonempty finite bases. States are positive semidefinite operators of trace one; pure kets have norm one. All marginal states below are partial traces of the stated joint state. Logarithms are natural, and spectral powers vanish on the kernel, including at exponent zero.
--
--   Let $\rho,\sigma$ be positive definite states and $\mathcal N$ a strict CPTP map. Define $L=\log\mathcal N(\rho)-\log\mathcal N(\sigma)$, $H=\log\rho-\log\sigma-\mathcal N^\dagger(L)$, and $d=D(\rho\|\sigma)-D(\mathcal N(\rho)\|\mathcal N(\sigma))$. For the full variance
--
--   $$V=\operatorname{Tr}\rho(H-dI)^2+\operatorname{Tr}\mathcal N(\rho)L^2-\operatorname{Tr}\rho[\mathcal N^\dagger(L)]^2,\qquad V\ge0.$$
--
--   All traces are real on these Hermitian expressions. The final correction is essential; the functional is not merely the ordinary variance of $H$. This supplies the nonnegative coefficient in Appendix B.
-- source:
--   Rényi squashed entanglement, discord, and relative entropy differences, arXiv:1410.1443v3, PDF p. 35, Unnumbered: non-negativity of relative-entropy-difference variance

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

/-- arXiv:1410.1443v3, PDF pp.35–36, (B.14)–(B.21): full variance nonnegativity. -/
theorem difference_variance_nonnegative (rho sigma : Op A) (N : Superop A B)
    (hrho : IsDensityMatrix rho) (hprho : rho.PosDef)
    (hsigma : IsDensityMatrix sigma) (hpsigma : sigma.PosDef) (hN : StrictChannel N) :
    0 ≤ differenceVariance rho sigma N := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P56

end
