-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P56_maximally_entangled_squashed
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P56.maximally_entangled_squashed
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:48:30.447127+00:00
-- url     : https://prove2.me/theorems/9cfcf390-f2b8-4e65-9ea4-ce3d24387eb6
-- title:
--   Corollary 14
-- statement:
--   All systems are finite-dimensional complex Hilbert spaces with nonempty finite bases. States are positive semidefinite operators of trace one; pure kets have norm one. All marginal states below are partial traces of the stated joint state. Logarithms are natural, and spectral powers vanish on the kernel, including at exponent zero.
--
--   Let $d\ge1$, let $\{|u_i\rangle\}_{i=1}^d$ and $\{|v_i\rangle\}_{i=1}^d$ be arbitrary orthonormal families, and let $|\Phi\rangle=d^{-1/2}\sum_i|u_i\rangle|v_i\rangle$. For $\alpha\in(0,1)\cup(1,2]$,
--
--   $$E^{\rm sq}_\alpha(A;B)_\Phi=\log d.$$
--
--   The Schmidt rank $d$ may be smaller than either ambient dimension. In particular $d=1$ gives zero. The equality fixes normalization in nats.
-- source:
--   Rényi squashed entanglement, discord, and relative entropy differences, arXiv:1410.1443v3, PDF p. 13, Corollary 14

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

/-- arXiv:1410.1443v3, PDF p.13, Corollary 14, (4.53).
Arbitrary orthonormal Schmidt families; d=1 is included. -/
theorem maximally_entangled_squashed (a : ℝ) (ha : DPOrder a)
    (d : ℕ) (hd : 0 < d) (U : Matrix A (Fin d) ℂ) (V : Matrix B (Fin d) ℂ)
    (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1) :
    renyiSquashed a (pureDensity (maxEntangledKet d U V)) = (Real.log d : EReal) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P56

end
