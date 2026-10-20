-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P07_theorem1
-- name    : QAlgorithms.Papers.Independent.Dependency50.P07.theorem1
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:22:47.995106+00:00
-- url     : https://prove2.me/theorems/9bf05bed-3176-438b-9438-b6817fb1c81c
-- title:
--   Classical–quantum common-randomness rate theorem
-- statement:
--   Let $E=\{p(x),\rho_x^Q\}_{x\in\mathcal X}$ be a finite ensemble of density operators, with a normalized nonnegative distribution and finite nonempty classical and quantum systems. Alice holds $X$ and Bob holds $Q$. Use iid source copies, free local operations and private randomness, no initial shared randomness, and noiseless one-way classical communication from Alice to Bob at rate $R\ge0$. Define $C(E,R)$ operationally by vanishing key disagreement, asymptotic Shannon key entropy, and an exponentially bounded common key alphabet. For a finite stochastic channel $p(u|x)$, put $U\to X\to Q$, and set $D^*(E,R)=\sup\{I(U;Q):I(U;X)-I(U;Q)\le R\}$. Then
--
--   $$C(E,R)=C^*(E,R)=R+D^*(E,R).$$
--
--   There is a maximizing auxiliary with $|\mathcal U|\le|\mathcal X|+1$. The theorem identifies the operational capacity with a finite-dimensional optimization, including the zero-communication endpoint.
-- source:
--   Distilling common randomness from bipartite quantum states, arXiv:quant-ph/0304196v2, PDF p. 6, Theorem 1: CR-rate theorem for classical-quantum correlations

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P07

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder

open Filter

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

open QAlgorithms.Papers.Independent.Information100.P04 (Measurement)

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Dependency50.P07

section CQStatements

variable {X Q Y T : Type} [Fintype X] [Fintype Q] [Fintype Y] [Fintype T]
  [DecidableEq X] [DecidableEq Q] [DecidableEq Y] [DecidableEq T]
  [Nonempty X] [Nonempty Q] [Nonempty Y] [Nonempty T]

/-- PDF p.6, Theorem 1: operational equality and an attaining auxiliary of size <= |X|+1. -/
theorem theorem1 (E : CQData X Q) (hE : E.Valid) (R : ℝ) (hR : 0 ≤ R) :
    crCapacity (cqDensity E) R = cStar E R ∧ cStar E R = R + dStar E R ∧
    ∃ V : Auxiliary X, V.size ≤ Fintype.card X + 1 ∧ auxCost E V ≤ R ∧
      auxIQ E V = dStar E R := by sorry

end CQStatements

end QAlgorithms.Papers.Independent.Dependency50.P07

end
