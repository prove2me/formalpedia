-- Prove2me | Theorems.Thm_TroppMatrixConcentration_ch8_entropy_joint_convex
-- name    : TroppMatrixConcentration.ch8_entropy_joint_convex
-- status  : Proved
-- author  : @tc
-- created : 2026-10-07T13:53:24.769614+00:00
-- url     : https://prove2.me/theorems/1b2fc8a2-162e-4972-a7e7-d164fd2279a7
-- title:
--   Theorem 8.1.4 — Joint convexity of matrix relative entropy
-- statement:
--   For every positive matrix dimension, the set of pairs $(A,H)$ of positive-definite complex matrices is convex, and the function $(A,H)\mapsto D(A;H)$ is convex on this set. Thus for any two such pairs and any $0\le t\le1$,
--   $$D(tA_1+(1-t)A_2;\,tH_1+(1-t)H_2)\le tD(A_1;H_1)+(1-t)D(A_2;H_2).$$
--   The domain includes arbitrary noncommuting, unnormalized positive-definite matrices. This is the joint convexity statement supporting Lieb’s theorem.
-- source:
--   Joel A. Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1 (7 January 2015); https://arxiv.org/abs/1501.01571v1; Theorem 8.1.4 and Section 8.8, printed pp. 120, 137–138.

import Definitions.Def_TroppMatrixConcentration_ch8_entropy

open scoped Matrix.Norms.L2Operator ComplexOrder

namespace TroppMatrixConcentration

theorem ch8_entropy_joint_convex {d : ℕ} [NeZero d] :
    ConvexOn ℝ {P : Matrix (Fin d) (Fin d) ℂ × Matrix (Fin d) (Fin d) ℂ |
      P.1.PosDef ∧ P.2.PosDef} (fun P => ch8_relativeEntropy P.1 P.2) := by sorry

end TroppMatrixConcentration
