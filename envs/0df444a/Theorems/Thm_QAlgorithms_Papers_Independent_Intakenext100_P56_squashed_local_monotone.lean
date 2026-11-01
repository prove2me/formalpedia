-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P56_squashed_local_monotone
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P56.squashed_local_monotone
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:38:04.515404+00:00
-- url     : https://prove2.me/theorems/b8936691-1f47-492f-97ee-93e85fb75e42
-- title:
--   Consequence 3
-- statement:
--   All systems are finite-dimensional complex Hilbert spaces with nonempty finite bases. States are positive semidefinite operators of trace one; pure kets have norm one. All marginal states below are partial traces of the stated joint state. Logarithms are natural, and spectral powers vanish on the kernel, including at exponent zero.
--
--   Assume Conjecture 1, namely first-register local monotonicity of the optimized Petz conditional mutual information (3.18), uniformly for every finite tripartite state and CPTP map. Let $\alpha\in(0,1)\cup(1,2]$, let $\rho_{AB}$ be a state, and let $\mathcal N:A\to A'$ and $\mathcal M:B\to B'$ be CPTP maps. With $\sigma=(\mathcal N\otimes\mathcal M)(\rho)$,
--
--   $$E^{\rm sq}_\alpha(A';B')_\sigma\le E^{\rm sq}_\alpha(A;B)_\rho.$$
--
--   Here $E^{\rm sq}_\alpha$ is one half the infimum of (3.18) over all finite normalized extensions, without any ancillary dimension cap. This establishes monotonicity under local operations.
-- source:
--   Rényi squashed entanglement, discord, and relative entropy differences, arXiv:1410.1443v3, PDF p. 8, Consequence 3

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

/-- arXiv:1410.1443v3, PDF p.8, Consequence 3, (4.2). -/
theorem squashed_local_monotone (hconjecture : LocalMonotonicityConjecture)
    (a : ℝ) (ha : DPOrder a) (rho : Op (A × B)) (hrho : IsDensityMatrix rho)
    (N : Superop A C) (M : Superop B D) (hN : IsChannel N) (hM : IsChannel M) :
    renyiSquashed a (idTensorSuperop M (applyFirstSuperop N rho)) ≤ renyiSquashed a rho := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P56

end
