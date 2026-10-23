-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P20_example4
-- name    : QAlgorithms.Papers.Independent.Frontier30.P20.example4
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T18:34:28.666409+00:00
-- url     : https://prove2.me/theorems/8a2911a0-607d-4a33-a621-946dfd0c8682
-- title:
--   Example 4 (negative-determinant channel)
-- statement:
--   All maps act complex-linearly on the same matrix algebra $M_d(\mathbb C)$, where $d\ge1$. Composition $AB$ applies $B$ first. Norms of maps are induced by the unnormalized Hilbert–Schmidt norm. Assume $d\ge2$. Let $T_c$ exchange entries $(1,d)$ and $(d,1)$ and fix all other matrix entries. The linear map
--
--   $$N_d(\rho)=\frac{\rho^{T_c}+I\operatorname{tr}\rho}{d+1}$$
--
--   is CPTP, has Kraus rank $d^2-1$, and has determinant $-(d+1)^{1-d^2}$. For $d=2$ it is entanglement breaking and
--
--   $$N_2(\rho)=\frac13\sum_{j=1}^6|\overline{\xi_j}\rangle\langle\xi_j|\rho|\xi_j\rangle\langle\overline{\xi_j}|,$$
--
--   where the $\xi_j$ are the six normalized Pauli eigenvectors, two per Pauli matrix.
--
--   This supplies negative-determinant channels in every nontrivial dimension.
-- source:
--   Dividing Quantum Channels, arXiv:math-ph/0611057v3, PDF p. 7, Example 4 (negative-determinant channel)

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P20

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Frontier30.P20

open QAlgorithms.Papers.Independent.Information100.P26 (Mat outer)

open QAlgorithms.Papers.Independent.Dependency50.P14 (Super)

-- Accepted matrix-unit coordinates on the action of a superoperator.

local notation "coefficients" =>
  QAlgorithms.Papers.Independent.Dependency50.P12.superOfAction

/-- Example 4, PDF pp.7--8: negative-determinant channel and its six-term qubit representation.
Source correction: d>=2 makes the two corners distinct; the printed d=1 claim is false. -/
theorem example4 :
    (∀ d : ℕ, 2 ≤ d → Channel (negativeChannel d) ∧
      krausRank (negativeChannel d) = d ^ 2 - 1 ∧
      complexDet (negativeChannel d) = (-((d + 1 : ℂ) ^ (1 - (d : ℤ) ^ 2)))) ∧
    (QAlgorithms.Entanglement.IsEntanglementBreakingPositive
      (negativeChannel 2).toLinearMap ∧
      negativeChannel 2 = (1 / 3 : ℂ) • ∑ j : Fin 6,
        twoSidedMap (outer (fun k => conj (pauliEigenvectors j k)) (pauliEigenvectors j))
          (outer (fun k => conj (pauliEigenvectors j k)) (pauliEigenvectors j))ᴴ) := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P20

end
