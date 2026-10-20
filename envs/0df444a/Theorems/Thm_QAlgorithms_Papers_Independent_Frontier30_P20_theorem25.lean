-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P20_theorem25
-- name    : QAlgorithms.Papers.Independent.Frontier30.P20.theorem25
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T18:53:07.985633+00:00
-- url     : https://prove2.me/theorems/6c5d004e-2eea-4c56-8d25-872d523cd36b
-- title:
--   Theorem 25 (Continuous positive evolutions)
-- statement:
--   Let $T$ be a CPTP map on $M_2(\mathbb C)$, a qubit channel. Composition applies the rightmost factor first; map norms are induced Hilbert–Schmidt norms. The endpoint remains CPTP, but allow positive TP maps in the arbitrarily fine product set $\mathcal I_{\mathrm{pos}}$. Then
--
--   $$T\in\overline{\mathcal I_{\mathrm{pos}}}\iff\det T\ge0.$$
--
--   The closure includes determinant-zero channels. This distinguishes positive evolutions from the more restrictive CP evolution criterion.
-- source:
--   Dividing Quantum Channels, arXiv:math-ph/0611057v3, PDF p. 22, Theorem 25 (Continuous positive evolutions)

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P20

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Frontier30.P20

open QAlgorithms.Papers.Independent.Information100.P26 (Mat outer)

open QAlgorithms.Papers.Independent.Dependency50.P14 (Super)

-- Accepted matrix-unit coordinates on the action of a superoperator.

local notation "coefficients" =>
  QAlgorithms.Papers.Independent.Dependency50.P12.superOfAction

/-- Theorem 25, PDF p.22: CPTP endpoints, but positive TP infinitesimal factors. -/
theorem theorem25 (T : Super 2) (hT : Channel T) :
    Infinitesimal false T ↔ 0 ≤ determinant T := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P20

end
