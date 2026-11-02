-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P97_ssa_endpoint_separable
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P97.ssa_endpoint_separable
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:39:20.602262+00:00
-- url     : https://prove2.me/theorems/d250424c-4649-459d-9ea1-8e4bbccfbcf9
-- title:
--   Remark 4: SSA equality gives separability and nonnegative endpoint conditional entropy
-- statement:
--   Let $\rho_{ABC}$ be a trace-one positive semidefinite density matrix on arbitrary finite-dimensional complex factors $A,B,C$ of positive dimension. All entropies are in bits and all marginals are actual partial traces of $\rho$. Use $S(X\mid Y)=S(XY)-S(Y)$ and $I(X;Z\mid Y)=S(XY)+S(YZ)-S(XYZ)-S(Y)$. Without assuming SSA equality,
--
--   $$
--   2S(A\mid C)+I(A;C\mid B)=[S(A\mid B)+S(A\mid C)]+I(A;B\mid C)\ge0.
--   $$
--
--   If $I(A;C\mid B)=0$, then $\rho_{AC}$ is separable, meaning a finite convex combination of product density matrices, and $S(A\mid C)\ge0$. This records the structural consequence while identifying the entropy conclusion as a consequence of the basic inequalities.
-- source:
--   A new inequality for the von Neumann entropy, arXiv:quant-ph/0406162v1, PDF p. 5, Remark 4

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P97

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P97

attribute [local instance] Classical.propDecidable Classical.decEq

local notation "A" => ({0} : Finset (Fin 4))

local notation "B" => ({1} : Finset (Fin 4))

local notation "C" => ({2} : Finset (Fin 4))

local notation "D" => ({3} : Finset (Fin 4))

/-- PDF p.5, Remark 4: the identity and nonnegativity are unconditional; SSA
equality additionally implies separability of AC and S(A|C) ≥ 0. -/
theorem ssa_endpoint_separable {X Y Z : Type*}
    [Fintype X] [Fintype Y] [Fintype Z] [Nonempty X] [Nonempty Y] [Nonempty Z]
    (rho : Matrix (X × (Y × Z)) (X × (Y × Z)) ℂ) (hrho : IsDensityMatrix rho) :
    let sab := vnEntropy (marginalAB3 rho)
    let sac := vnEntropy (marginalAC3 rho)
    let sbc := vnEntropy (traceLeft rho)
    let sa := vnEntropy (traceRight (marginalAB3 rho))
    let sb := vnEntropy (traceLeft (marginalAB3 rho))
    let sc := vnEntropy (traceLeft (marginalAC3 rho))
    let sabc := vnEntropy rho
    let acGivenB := sab + sbc - sabc - sb
    let abGivenC := sac + sbc - sabc - sc
    (2 * (sac - sc) + acGivenB = (sab - sb) + (sac - sc) + abGivenC) ∧
    0 ≤ (sab - sb) + (sac - sc) + abGivenC ∧
    (acGivenB = 0 → Entanglement.IsSeparableDensity (marginalAC3 rho) ∧ 0 ≤ sac - sc) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P97

end
