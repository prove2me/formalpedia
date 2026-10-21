-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P20_theorem11
-- name    : QAlgorithms.Papers.Independent.Frontier30.P20.theorem11
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T18:40:12.070683+00:00
-- url     : https://prove2.me/theorems/11dd3140-8d35-493e-8616-41ce8f1b3357
-- title:
--   Theorem 11 (Divisibility of generic channels)
-- statement:
--   All maps act complex-linearly on the same matrix algebra $M_d(\mathbb C)$, where $d\ge1$. Composition $AB$ applies $B$ first. Norms of maps are induced by the unnormalized Hilbert–Schmidt norm. Let $d\ge2$ and let $T$ be a channel of Kraus rank $d^2$. Then
--
--   $$T=AB$$
--
--   for CPTP maps $A,B$ neither of which is a unitary conjugation.
--
--   Thus full Choi rank ensures nontrivial two-factor divisibility.
-- source:
--   Dividing Quantum Channels, arXiv:math-ph/0611057v3, PDF p. 12, Theorem 11 (Divisibility of generic channels)

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P20

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Frontier30.P20

open QAlgorithms.Papers.Independent.Information100.P26 (Mat outer)

open QAlgorithms.Papers.Independent.Dependency50.P14 (Super)

-- Accepted matrix-unit coordinates on the action of a superoperator.

local notation "coefficients" =>
  QAlgorithms.Papers.Independent.Dependency50.P12.superOfAction

/-- Theorem 11, PDF p.12: a nontrivial CPTP factorization at full Choi rank.
Source correction: d>=2; the d=1 channel is unitary and indivisible. -/
theorem theorem11 {d : ℕ} (hd : 2 ≤ d) (T : Super d)
    (hT : Channel T) (hrank : krausRank T = d ^ 2) : Divisible true T := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P20

end
