-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P56_petz_difference_near_one
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P56.petz_difference_near_one
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:04:14.273694+00:00
-- url     : https://prove2.me/theorems/32b9c82d-e91a-4719-97d3-fb664ab0723a
-- title:
--   Unnumbered: Petz difference monotonicity near one, as proved in Appendix B
-- statement:
--   All systems are finite-dimensional complex Hilbert spaces with nonempty finite bases. States are positive semidefinite operators of trace one; pure kets have norm one. All marginal states below are partial traces of the stated joint state. Logarithms are natural, and spectral powers vanish on the kernel, including at exponent zero.
--
--   Let $\rho,\sigma$ be positive definite states and $\mathcal N$ a strict CPTP map. Suppose the full computed variance $V(\rho,\sigma,\mathcal N)$ of (B.14) is strictly positive. Then there exists an instance-dependent $0<\eta<1$ such that
--
--   $$1-\eta<\alpha\le\beta<1+\eta\quad\Longrightarrow\quad\Delta_\alpha(\rho,\sigma,\mathcal N)\le\Delta_\beta(\rho,\sigma,\mathcal N).$$
--
--   The one endpoint uses the ordinary relative entropy relativeEntropyDifference. This states the Petz neighborhood monotonicity justified in Appendix B; it does not include the explicitly unhandled case $V=0$ or assert a sandwiched analogue.
-- source:
--   Rényi squashed entanglement, discord, and relative entropy differences, arXiv:1410.1443v3, PDF p. 26, Unnumbered: Petz difference monotonicity near one, as proved in Appendix B

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

/-- arXiv:1410.1443v3, PDF pp.34–37, Appendix B: PETZ local monotonicity
under the proof's explicit V>0 condition. Neighborhood depends on rho,sigma,N. -/
theorem petz_difference_near_one (rho sigma : Op A) (N : Superop A B)
    (hrho : IsDensityMatrix rho) (hprho : rho.PosDef)
    (hsigma : IsDensityMatrix sigma) (hpsigma : sigma.PosDef) (hN : StrictChannel N)
    (hV : 0 < differenceVariance rho sigma N) :
    ∃ eta : ℝ, 0 < eta ∧ eta < 1 ∧
      MonotoneOn (fun a : ℝ => differencePetz a rho sigma N) (Set.Ioo (1-eta) (1+eta)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P56

end
