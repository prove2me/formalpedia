-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P56_squashed_LOCC_monotone
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P56.squashed_LOCC_monotone
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:40:00.103931+00:00
-- url     : https://prove2.me/theorems/4fc3028e-4203-4a45-bd37-147d6b707528
-- title:
--   Consequence 5
-- statement:
--   All systems are finite-dimensional complex Hilbert spaces with nonempty finite bases. States are positive semidefinite operators of trace one; pure kets have norm one. All marginal states below are partial traces of the stated joint state. Logarithms are natural, and spectral powers vanish on the kernel, including at exponent zero.
--
--   Assume Conjecture 1. For $\alpha\in(0,1)\cup(1,2]$, every state $\rho_{AB}$ and every finite adaptive LOCC protocol $\mathcal L:AB\to A'B'$ satisfy
--
--   $$E^{\rm sq}_\alpha(A';B')_{\mathcal L(\rho)}\le E^{\rm sq}_\alpha(A;B)_\rho.$$
--
--   LOCC is an actual finite tree of complete local Kraus instruments with outcome-dependent continuation, arbitrary intermediate dimensions, ancillary preparation and disposal. This is monotonicity of the complete output, without an average-branch claim.
-- source:
--   Rényi squashed entanglement, discord, and relative entropy differences, arXiv:1410.1443v3, PDF p. 10, Consequence 5

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

/-- arXiv:1410.1443v3, PDF p.10, Consequence 5. No average-branch strengthening. -/
theorem squashed_LOCC_monotone (hconjecture : LocalMonotonicityConjecture)
    (a : ℝ) (ha : DPOrder a) : SquashedLOCC a := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P56

end
