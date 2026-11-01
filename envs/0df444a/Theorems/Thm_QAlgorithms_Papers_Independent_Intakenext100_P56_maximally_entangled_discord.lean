-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P56_maximally_entangled_discord
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P56.maximally_entangled_discord
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:53:57.894703+00:00
-- url     : https://prove2.me/theorems/9a0fb499-557d-4268-80fe-6b62f6cf1d8e
-- title:
--   Corollary 22
-- statement:
--   All systems are finite-dimensional complex Hilbert spaces with nonempty finite bases. States are positive semidefinite operators of trace one; pure kets have norm one. All marginal states below are partial traces of the stated joint state. Logarithms are natural, and spectral powers vanish on the kernel, including at exponent zero.
--
--   Let $|\Phi\rangle=d^{-1/2}\sum_{i=1}^d|u_i\rangle_A|v_i\rangle_B$, where $d=\dim A\ge1$ and both Schmidt families are orthonormal. For $\alpha\in(0,1)\cup(1,2]$,
--
--   $$D_\alpha(\bar A;B)_\Phi=\log\dim A.$$
--
--   An unused orthogonal complement in $B$ is allowed. The optimization still ranges over arbitrary rank-one POVMs; the proof's equal-probability sentence is not used to restrict them.
-- source:
--   Rényi squashed entanglement, discord, and relative entropy differences, arXiv:1410.1443v3, PDF p. 21, Corollary 22

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

/-- arXiv:1410.1443v3, PDF p.21, Corollary 22, (5.40).
Schmidt rank equals |A|; B may contain an unused orthogonal complement. -/
theorem maximally_entangled_discord (a : ℝ) (ha : DPOrder a)
    (d : ℕ) (hd : 0 < d) (hdA : d = Fintype.card A)
    (U : Matrix A (Fin d) ℂ) (V : Matrix B (Fin d) ℂ)
    (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1) :
    renyiDiscord a (pureDensity (maxEntangledKet d U V)) =
      (Real.log (Fintype.card A) : EReal) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P56

end
