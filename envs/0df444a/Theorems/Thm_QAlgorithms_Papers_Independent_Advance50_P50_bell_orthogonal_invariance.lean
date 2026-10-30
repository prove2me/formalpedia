-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P50_bell_orthogonal_invariance
-- name    : QAlgorithms.Papers.Independent.Advance50.P50.bell_orthogonal_invariance
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T11:13:30.904089+00:00
-- url     : https://prove2.me/theorems/06d0f835-4320-42e8-8f0e-5623d3a1053a
-- title:
--   Unnumbered Bell-observable invariance, proof of Theorem 4
-- statement:
--   Fix $n\ge0$ and $d=2^n$. In the computational basis define the literal vector printed in Eq.(22),
--
--   $$v=\frac1d\sum_{x\in\{0,1\}^n}|x\rangle|x\rangle.$$
--
--   For the real orthogonal subgroup $O(d)\subseteq U(d)$,
--
--   $$|v\rangle\langle v|\in C^{(2)}(O(d)),\qquad \|v\|^2=\frac1d.$$
--
--   Thus its outer product is a quadratic symmetry. For $n>0$ this vector is not a normalized quantum state; no classification claim is attached to it.
-- source:
--   Group-Invariant Quantum Machine Learning, arXiv:2205.02261v2, PDF p. 10, Unnumbered Bell-observable invariance, proof of Theorem 4

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P50

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P50

open MeasureTheory ProbabilityTheory

open scoped ComplexConjugate ENNReal

-- Exact accepted primitives; no paper-local redeclarations.

open QAlgorithms.Papers.Independent.Information100.P63 (Mat tensorPower)

open QAlgorithms.Papers.Independent.Gap48.P20 (Copies)

open QAlgorithms.Papers.Independent.Gap48.P38 (subsystemReduction)

open QAlgorithms.Papers.Independent.Information100.P32 (purity)

open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)

-- Matrices carry the associative commutator bracket X*Y-Y*X.

attribute [local instance 100] LieRing.ofAssociativeRing

/-- PDF pp.10–11, Eq.(23): the outer product of the literal printed Bell
vector is a quadratic orthogonal symmetry. Its norm squared is 1/d, not 1. -/
theorem bell_orthogonal_invariance (n : ℕ) :
    pureDensity (printedBell n) ∈ tensorCommutant 2 (orthogonalMatrices n) ∧
    ‖printedBell n‖ ^ 2 = 1 / (2 : ℝ) ^ n := by sorry

end QAlgorithms.Papers.Independent.Advance50.P50

end
