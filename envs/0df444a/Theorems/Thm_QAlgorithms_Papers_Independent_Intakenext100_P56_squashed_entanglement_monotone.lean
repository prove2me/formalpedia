-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P56_squashed_entanglement_monotone
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P56.squashed_entanglement_monotone
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:41:51.517986+00:00
-- url     : https://prove2.me/theorems/41d7e8e2-ce00-4a7f-9570-b60a0efa0edf
-- title:
--   Consequence 7
-- statement:
--   All systems are finite-dimensional complex Hilbert spaces with nonempty finite bases. States are positive semidefinite operators of trace one; pure kets have norm one. All marginal states below are partial traces of the stated joint state. Logarithms are natural, and spectral powers vanish on the kernel, including at exponent zero.
--
--   Assume Conjecture 1 and let $0<\alpha<1$. Then $E^{\rm sq}_\alpha$ is both monotone under every finite adaptive LOCC protocol and convex over every normalized finite ensemble:
--
--   $$E^{\rm sq}_\alpha(\mathcal L(\rho))\le E^{\rm sq}_\alpha(\rho),\qquad E^{\rm sq}_\alpha\!\left(\sum_xp_x\rho^x\right)\le\sum_xp_xE^{\rm sq}_\alpha(\rho^x).$$
--
--   These two properties are exactly the paper's definition of an entanglement monotone.
-- source:
--   Rényi squashed entanglement, discord, and relative entropy differences, arXiv:1410.1443v3, PDF p. 10, Consequence 7

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

/-- arXiv:1410.1443v3, PDF pp.8,10, Consequence 7: both defining properties. -/
theorem squashed_entanglement_monotone (hconjecture : LocalMonotonicityConjecture)
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    SquashedLOCC a ∧ SquashedConvex a := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P56

end
