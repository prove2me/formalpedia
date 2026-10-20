-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P20_theorem24
-- name    : QAlgorithms.Papers.Independent.Frontier30.P20.theorem24
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T18:52:27.210554+00:00
-- url     : https://prove2.me/theorems/11c63de9-7369-41cb-bfd1-4cd236fd4a6c
-- title:
--   Theorem 24 (Characterization of infinitesimal divisible channels)
-- statement:
--   Let $T$ be a CPTP map on $M_2(\mathbb C)$, a qubit channel. Composition applies the rightmost factor first; map norms are induced Hilbert–Schmidt norms. Let $\Delta$ be the real $3\times3$ block of a Lorentz normal representative of $T$, and let $s_{\min}$ be its least singular value. Then $T$ is infinitesimal divisible within CPTP, with ambient norm closure, exactly when a normal representative satisfies one of
--
--   $$\text{non-diagonal branch},\qquad\text{diagonal branch and }\operatorname{rank}\Delta<2,\qquad\text{diagonal branch and }s_{\min}^2\ge\det\Delta>0.$$
--
--   The non-diagonal alternative includes the singular constant-output branch, whose translation vector is nonzero even though $\Delta=0$.
--
--   This criterion includes singular limits and the equality case in the positive-determinant inequality.
-- source:
--   Dividing Quantum Channels, arXiv:math-ph/0611057v3, PDF p. 20, Theorem 24 (Characterization of infinitesimal divisible channels)

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P20

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Frontier30.P20

open QAlgorithms.Papers.Independent.Information100.P26 (Mat outer)

open QAlgorithms.Papers.Independent.Dependency50.P14 (Super)

-- Accepted matrix-unit coordinates on the action of a superoperator.

local notation "coefficients" =>
  QAlgorithms.Papers.Independent.Dependency50.P12.superOfAction

/-- Theorem 24, PDF pp.20--22: the full three-branch classification, including singular endpoints. -/
theorem theorem24 (T : Super 2) (hT : Channel T) :
    Infinitesimal true T ↔ ∃ S : Super 2, NormalRepresentative T S ∧
      (OtherBranch S ∨
        (DiagonalBranch S ∧ (pauliBlock S).rank < 2) ∨
        (DiagonalBranch S ∧ SingularCriterion (pauliBlock S))) := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P20

end
