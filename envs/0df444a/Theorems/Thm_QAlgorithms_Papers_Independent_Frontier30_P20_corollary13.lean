-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P20_corollary13
-- name    : QAlgorithms.Papers.Independent.Frontier30.P20.corollary13
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T18:42:10.424875+00:00
-- url     : https://prove2.me/theorems/3894106c-f8a9-4758-a794-ed9301d1f13f
-- title:
--   Corollary 13 (Reduction to normal form)
-- statement:
--   All maps act complex-linearly on the same matrix algebra $M_d(\mathbb C)$, where $d\ge1$. Composition $AB$ applies $B$ first. Norms of maps are induced by the unnormalized Hilbert–Schmidt norm. Choose the positive TP or CPTP class $\mathcal T$. If $T,R\in\mathcal T$ and $T=ARB$, where $A(X)=K_A X K_A^\dagger$ and $B(X)=K_B X K_B^\dagger$ for invertible matrices $K_A,K_B$, then
--
--   $$T\text{ is divisible in }\mathcal T\iff R\text{ is divisible in }\mathcal T.$$
--
--   The filters need not preserve trace. This enables reduction of divisibility to filtering normal forms.
-- source:
--   Dividing Quantum Channels, arXiv:math-ph/0611057v3, PDF p. 12, Corollary 13 (Reduction to normal form)

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P20

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Frontier30.P20

open QAlgorithms.Papers.Independent.Information100.P26 (Mat outer)

open QAlgorithms.Papers.Independent.Dependency50.P14 (Super)

-- Accepted matrix-unit coordinates on the action of a superoperator.

local notation "coefficients" =>
  QAlgorithms.Papers.Independent.Dependency50.P12.superOfAction

/-- Corollary 13, PDF p.12: filtering preserves two-factor divisibility in either cone. -/
theorem corollary13 {d : ℕ} (hd : 0 < d) (completely : Bool) (T R A B : Super d)
    (hT : InClass completely T) (hR : InClass completely R)
    (hA : FilterMap A) (hB : FilterMap B) (hprod : T = A * R * B) :
    Divisible completely T ↔ Divisible completely R := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P20

end
