-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P49_canonicalCompositionTable
-- name    : QAlgorithms.Papers.Independent.Claimed50.P49.canonicalCompositionTable
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:07:15.288726+00:00
-- url     : https://prove2.me/theorems/45858f30-8440-44e2-b1f2-1a4c61133c00
-- title:
--   Canonical composition table with product-one branch
-- statement:
--   Use the six canonical forms $A_1,A_2,B_1,B_2,C,D$ of Table 1 on the full one-mode Fock space. Their noise parameter is $N\ge0$; the amplitude $\kappa$ is positive for $C,D$, and $\kappa
--   e1$ for $C$. The $B_1$ noise is fixed to $\operatorname{diag}(0,1/2)$, and $B_2(0)$ is the identity. For two canonical representatives, compose their data by (2.6). The class of the result lies in the entry below; rows are the second map and columns the first:
--
--   $$\begin{array}{c|cccccc}\circ&A_1&A_2&B_1&B_2&C&D\\\hline A_1&A_1&A_1&A_1&A_1&A_1&A_1\\A_2&A_1&A_2&A_2&A_2&A_2&A_2\\B_1&A_1&A_2&B_1&B_1/B_2&C&D\\B_2&A_1&A_2&B_1/B_2&B_2&C&D\\C&A_1&A_2&C&C&B_2/C&D\\D&A_1&A_2&D&D&D&B_2/C\end{array}$$
--
--   For the $D,D$ entry, the result is $B_2$ exactly when $\kappa_1\kappa_2=1$. Classification uses the determinant/rank invariants of Table 1. The rule concerns the fixed canonical representatives and permits subsequent canonical equivalence of the result.
-- source:
--   One-mode Bosonic Gaussian channels: a full weak-degradability classification, arXiv:quant-ph/0609013v2, PDF p. 11, (2.18)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P49

noncomputable section

open scoped BigOperators ENNReal Topology

open Filter MeasureTheory

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)

open QAlgorithms.Papers.Independent.Frontier30.P14

open QAlgorithms.Papers.Independent.Information100.P37 (quadratic)

namespace QAlgorithms.Papers.Independent.Claimed50.P49

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- Equation (2.18), PDF p.11: all table entries for the fixed canonical axes.
Printed D composed D=C is corrected to B2/C at product-one gain, as forced by
(2.6). The exact product-one branch is retained. Independent moderation required. -/
theorem canonicalCompositionTable (c1 c2 : CanonicalClass) (k1 k2 N1 N2 : ℝ)
    (h1 : ValidSourceCanonical c1 k1 N1) (h2 : ValidSourceCanonical c2 k2 N2) :
    classOf (composeData (canonicalData c1 k1 N1) (canonicalData c2 k2 N2)) ∈
      compositionClasses c2 c1 ∧
    (c1 = .D → c2 = .D →
      (classOf (composeData (canonicalData c1 k1 N1) (canonicalData c2 k2 N2)) = .B2 ↔
        k1 * k2 = 1)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P49

end
