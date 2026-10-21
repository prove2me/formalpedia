-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P20_theorem12
-- name    : QAlgorithms.Papers.Independent.Frontier30.P20.theorem12
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T18:41:11.920988+00:00
-- url     : https://prove2.me/theorems/f1be3dd9-9a45-49ae-aafa-2ab2172f56e0
-- title:
--   Theorem 12 (trace-preserving normalization of factors)
-- statement:
--   All maps act complex-linearly on the same matrix algebra $M_d(\mathbb C)$, where $d\ge1$. Composition $AB$ applies $B$ first. Norms of maps are induced by the unnormalized Hilbert–Schmidt norm. Choose either the positive or the completely positive cone $\mathcal P$, and let $\mathcal T$ be its TP subset. Suppose $AB=T$, $A,B\in\mathcal P$, $T\in\mathcal T$, and $\det(A^*(I))
--   e0$, where $A^*$ is the Hilbert–Schmidt adjoint. Then there exist $R,S\in\mathcal T$ such that
--
--   $$RS=T,\qquad\operatorname{rank}J(R)=\operatorname{rank}J(A),\qquad\operatorname{rank}J(S)=\operatorname{rank}J(B).$$
--
--   Here $J$ is the normalized Choi operator; its rank is used even when the maps are only positive. This removes trace constraints from preliminary factor searches without changing individual ranks.
-- source:
--   Dividing Quantum Channels, arXiv:math-ph/0611057v3, PDF p. 12, Theorem 12 (trace-preserving normalization of factors)

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P20

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Frontier30.P20

open QAlgorithms.Papers.Independent.Information100.P26 (Mat outer)

open QAlgorithms.Papers.Independent.Dependency50.P14 (Super)

-- Accepted matrix-unit coordinates on the action of a superoperator.

local notation "coefficients" =>
  QAlgorithms.Papers.Independent.Dependency50.P12.superOfAction

/-- Theorem 12, PDF p.12: normalization in both cones, preserving each Choi rank. -/
theorem theorem12 {d : ℕ} (hd : 0 < d) (completely : Bool) (A B T : Super d)
    (hA : Cone completely A) (hB : Cone completely B)
    (hT : InClass completely T) (hprod : A * B = T) (hinv : (dualIdentity A).det ≠ 0) :
    ∃ R S : Super d, InClass completely R ∧ InClass completely S ∧
      krausRank R = krausRank A ∧ krausRank S = krausRank B ∧ R * S = T := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P20

end
