-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P56_difference_limit_one
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P56.difference_limit_one
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:01:24.932503+00:00
-- url     : https://prove2.me/theorems/f2a5b122-d354-40ff-a6b1-30671db4def3
-- title:
--   Unnumbered: Definition 25 convergence at alpha=1
-- statement:
--   All systems are finite-dimensional complex Hilbert spaces with nonempty finite bases. States are positive semidefinite operators of trace one; pure kets have norm one. All marginal states below are partial traces of the stated joint state. Logarithms are natural, and spectral powers vanish on the kernel, including at exponent zero.
--
--   Let $\rho,\sigma$ be positive definite density operators and $\mathcal N$ a strict CPTP map. Let $\Delta_\alpha$ and $\widetilde\Delta_\alpha$ be the actual trace formulas (6.12) and the well-typed Schatten formula (6.13)/(6.18). Then
--
--   $$\lim_{\alpha\to1,\,\alpha\ne1}\Delta_\alpha(\rho,\sigma,\mathcal N)=\lim_{\alpha\to1,\,\alpha\ne1}\widetilde\Delta_\alpha(\rho,\sigma,\mathcal N)=D(\rho\|\sigma)-D(\mathcal N(\rho)\|\mathcal N(\sigma)).$$
--
--   The punctured positive-order limit is two-sided near one and assumes no parameter-monotonicity conjecture. It fixes the continuous endpoint of both generalizations.
-- source:
--   Rényi squashed entanglement, discord, and relative entropy differences, arXiv:1410.1443v3, PDF p. 25, Unnumbered: Definition 25 convergence at alpha=1

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

/-- arXiv:1410.1443v3, PDF p.25: both Definition 25 functionals converge
at one; this assertion is unconditional and is not Conjecture 26. -/
theorem difference_limit_one (rho sigma : Op A) (N : Superop A B)
    (hrho : IsDensityMatrix rho) (hprho : rho.PosDef)
    (hsigma : IsDensityMatrix sigma) (hpsigma : sigma.PosDef) (hN : StrictChannel N) :
    Tendsto (fun a : ℝ => differencePetz a rho sigma N)
      (nhdsWithin 1 {a : ℝ | 0 < a ∧ a ≠ 1}) (nhds (relativeEntropyDifference rho sigma N)) ∧
    Tendsto (fun a : ℝ => differenceSandwiched a rho sigma N)
      (nhdsWithin 1 {a : ℝ | 0 < a ∧ a ≠ 1}) (nhds (relativeEntropyDifference rho sigma N)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P56

end
