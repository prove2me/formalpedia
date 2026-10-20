-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P20_identity_vicinity
-- name    : QAlgorithms.Papers.Independent.Frontier30.P20.identity_vicinity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T18:53:55.583884+00:00
-- url     : https://prove2.me/theorems/b9cb90d6-704d-4dbf-bd02-fc4dc7ce0632
-- title:
--   Unnumbered main observation (all divisibility types near identity)
-- statement:
--   Let $T$ be a CPTP map on $M_2(\mathbb C)$, a qubit channel. Composition applies the rightmost factor first; map norms are induced Hilbert–Schmidt norms. For every $\varepsilon>0$, each of the following four predicates has a CPTP qubit witness $T$ satisfying
--
--   $$\|T-\mathrm{id}\|<\varepsilon:$$
--
--   (1) indivisibility within CPTP; (2) divisibility within CPTP; (3) failure of infinitesimal divisibility within CPTP; (4) Markovianity. Different predicates may use different witnesses, and they are not asserted to form an exclusive partition.
--
--   This records the coexistence of the named divisibility types arbitrarily close to the ideal channel.
--
--   The indivisible witness is required to be nonunitary; the identity does not supply that witness.
-- source:
--   Dividing Quantum Channels, arXiv:math-ph/0611057v3, PDF p. 22, Unnumbered main observation (all divisibility types near identity)

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P20

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Frontier30.P20

open QAlgorithms.Papers.Independent.Information100.P26 (Mat outer)

open QAlgorithms.Papers.Independent.Dependency50.P14 (Super)

-- Accepted matrix-unit coordinates on the action of a superoperator.

local notation "coefficients" =>
  QAlgorithms.Papers.Independent.Dependency50.P12.superOfAction

/-- Main observation, PDF pp.3,19,22: each named type has witnesses in every identity neighborhood.
The indivisible witness is nonunitary, as in the rank-three classification. -/
theorem identity_vicinity (eps : ℝ) (heps : 0 < eps) :
    (∃ T : Super 2, Channel T ∧ hsOperatorNorm (T - 1) < eps ∧
      ¬ IsUnitaryConjugation T ∧ Indivisible true T) ∧
    (∃ T : Super 2, Channel T ∧ hsOperatorNorm (T - 1) < eps ∧ Divisible true T) ∧
    (∃ T : Super 2, Channel T ∧ hsOperatorNorm (T - 1) < eps ∧ ¬ Infinitesimal true T) ∧
    (∃ T : Super 2, Channel T ∧ hsOperatorNorm (T - 1) < eps ∧ Markovian T) := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P20

end
