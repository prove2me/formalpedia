-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P48_dual_stinespring
-- name    : QAlgorithms.Papers.Independent.Claimed50.P48.dual_stinespring
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:58:23.766586+00:00
-- url     : https://prove2.me/theorems/ac41adc5-edeb-492b-82c7-bb31ade09e7d
-- title:
--   Equation (21): equivalence of Schroedinger and Heisenberg dilations
-- statement:
--   Let $\Phi$ be a finite-dimensional CP map with nonzero input, and define its linear trace-dual by $\operatorname{Tr}(\Phi(X)Y)=\operatorname{Tr}(X\Phi^*(Y))$ for all operators $X,Y$. For every linear $V:H_A\to H_B\otimes H_C$,
--
--   $$\bigl[\Phi(X)=\operatorname{Tr}_C(VXV^*)\ \text{for every }X\bigr]
--   \quad\Longleftrightarrow\quad
--   \bigl[\Phi^*(Y)=V^*(Y\otimes I_C)V\ \text{for every }Y\bigr].$$
--
--   The trace-pairing identity is also part of the assertion, with the dual computed from matrix-unit coefficients. This identifies the Schroedinger and Heisenberg dilation formulas without assuming an unrelated dual map.
-- source:
--   On complementary channels and the additivity problem, arXiv:quant-ph/0509101v3, PDF p. 11, Equation (21): equivalence of Schroedinger and Heisenberg dilations

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P48

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P48

open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder ENNReal

open QAlgorithms.Papers.Independent.Information100.P67 (receiverChannel complementaryChannel environmentSwap)

open QAlgorithms.Papers.Independent.Information100.P03 (PureEnsemble convexRoof)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P60 (wernerHolevo)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C D A2 B2 C2 K : Type*}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

variable [Fintype A2] [DecidableEq A2] [Fintype B2] [DecidableEq B2]

variable [Fintype C2] [DecidableEq C2] [Fintype K] [DecidableEq K]

/-- Equation (21), PDF pp.10–11: computed trace-dual, trace pairing,
and equivalence with the Schroedinger partial-trace formula. -/
theorem dual_stinespring [Nonempty A] (Phi : Superop A B) (hPhi : FiniteKrausCP Phi)
    (V : Matrix (B × C) A ℂ) :
    (∀ rho X, (Phi rho * X).trace = (rho * operatorTraceDual Phi X).trace) ∧
    ((∀ rho, Phi rho = receiverChannel V rho) ↔
      ∀ X, operatorTraceDual Phi X = Vᴴ * (X ⊗ₖ (1 : Matrix C C ℂ)) * V) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P48

end
