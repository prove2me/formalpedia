-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P20_proposition15
-- name    : QAlgorithms.Papers.Independent.Frontier30.P20.proposition15
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T18:44:08.864119+00:00
-- url     : https://prove2.me/theorems/1bef8d4d-9c65-4ef0-82e4-8fabd57a8e65
-- title:
--   Proposition 15 (determinant obstruction)
-- statement:
--   All maps act complex-linearly on the same matrix algebra $M_d(\mathbb C)$, where $d\ge1$. Composition $AB$ applies $B$ first. Norms of maps are induced by the unnormalized Hilbert–Schmidt norm. For a channel $T$, membership in the ambient norm closure $\overline{\mathcal I}$ of the arbitrarily fine exact CPTP product set implies
--
--   $$\det T\ge0.$$
--
--   The complex determinant is real. Singular boundary channels are included. This gives a necessary obstruction to infinitesimal divisibility.
-- source:
--   Dividing Quantum Channels, arXiv:math-ph/0611057v3, PDF p. 13, Proposition 15 (determinant obstruction)

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P20

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Frontier30.P20

open QAlgorithms.Papers.Independent.Information100.P26 (Mat outer)

open QAlgorithms.Papers.Independent.Dependency50.P14 (Super)

-- Accepted matrix-unit coordinates on the action of a superoperator.

local notation "coefficients" =>
  QAlgorithms.Papers.Independent.Dependency50.P12.superOfAction

/-- Proposition 15, PDF p.13: the determinant obstruction includes singular boundary channels. -/
theorem proposition15 {d : ℕ} (hd : 0 < d) (T : Super d)
    (hT : Channel T) (hinf : Infinitesimal true T) :
    (complexDet T).im = 0 ∧ 0 ≤ determinant T := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P20

end
