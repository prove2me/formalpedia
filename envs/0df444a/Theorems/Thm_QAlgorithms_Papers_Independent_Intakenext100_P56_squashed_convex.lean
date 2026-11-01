-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P56_squashed_convex
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P56.squashed_convex
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:41:10.179079+00:00
-- url     : https://prove2.me/theorems/0364b0da-653c-4800-b24c-b8400191c879
-- title:
--   Proposition 6
-- statement:
--   All systems are finite-dimensional complex Hilbert spaces with nonempty finite bases. States are positive semidefinite operators of trace one; pure kets have norm one. All marginal states below are partial traces of the stated joint state. Logarithms are natural, and spectral powers vanish on the kernel, including at exponent zero.
--
--   Let $0<\alpha<1$, let $p_x$ be any finite probability law, and let $\rho^x_{AB}$ be states. Writing $\bar\rho=\sum_xp_x\rho^x$, one has
--
--   $$E^{\rm sq}_\alpha(A;B)_{\bar\rho}\le\sum_xp_xE^{\rm sq}_\alpha(A;B)_{\rho^x}.$$
--
--   The assertion is uniform over every such ensemble and does not assume Conjecture 1. It establishes convexity of the measure.
-- source:
--   Rényi squashed entanglement, discord, and relative entropy differences, arXiv:1410.1443v3, PDF p. 10, Proposition 6

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

/-- arXiv:1410.1443v3, PDF p.10, Proposition 6, (4.19). Unconditional. -/
theorem squashed_convex (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    SquashedConvex a := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P56

end
