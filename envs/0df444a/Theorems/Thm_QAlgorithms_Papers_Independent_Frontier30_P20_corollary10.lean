-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P20_corollary10
-- name    : QAlgorithms.Papers.Independent.Frontier30.P20.corollary10
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T18:39:30.142565+00:00
-- url     : https://prove2.me/theorems/d9cab41c-63a1-42ac-b214-c98180eb0404
-- title:
--   Corollary 10 (Indivisible completely positive maps)
-- statement:
--   All maps act complex-linearly on the same matrix algebra $M_d(\mathbb C)$, where $d\ge1$. Composition $AB$ applies $B$ first. Norms of maps are induced by the unnormalized Hilbert–Schmidt norm. For every $d\ge1$, the determinant attains its minimum on the CPTP maps, and every minimizer $T_0$ is indivisible. Explicitly,
--
--   $$\exists T_0\text{ CPTP},\quad\forall R\text{ CPTP},\quad\det T_0\le\det R.$$
--
--   For $d=2$ the channel $N_2(\rho)=(\rho^T+I\operatorname{tr}\rho)/3$ is one such indivisible minimizer.
--
--   This gives indivisible channels in every nontrivial dimension without asserting uniqueness of the minimizer.
-- source:
--   Dividing Quantum Channels, arXiv:math-ph/0611057v3, PDF p. 11, Corollary 10 (Indivisible completely positive maps)

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P20

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Frontier30.P20

open QAlgorithms.Papers.Independent.Information100.P26 (Mat outer)

open QAlgorithms.Papers.Independent.Dependency50.P14 (Super)

-- Accepted matrix-unit coordinates on the action of a superoperator.

local notation "coefficients" =>
  QAlgorithms.Papers.Independent.Dependency50.P12.superOfAction

/-- Corollary 10, PDF pp.11--12: attainment, all minimizers indivisible, and the canonical qubit minimizer.
Dimension one is included: its unique channel is the indivisible identity. -/
theorem corollary10 :
    (∀ d : ℕ, 0 < d →
      (∃ T : Super d, Channel T ∧ ∀ R : Super d, Channel R → determinant T ≤ determinant R) ∧
      (∀ T : Super d, Channel T →
        (∀ R : Super d, Channel R → determinant T ≤ determinant R) → Indivisible true T)) ∧
    (Channel (negativeChannel 2) ∧ Indivisible true (negativeChannel 2) ∧
      ∀ R : Super 2, Channel R → determinant (negativeChannel 2) ≤ determinant R) := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P20

end
