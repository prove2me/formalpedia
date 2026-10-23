-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P16_inducedZeros_noCancellation
-- name    : QAlgorithms.Papers.Independent.Dependency50.P16.inducedZeros_noCancellation
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T08:37:33.126222+00:00
-- url     : https://prove2.me/theorems/96f7e5af-685d-4470-b66d-c8ed1f984ad7
-- title:
--   Lemma B.1: Zeros cannot cancel in induced generators
-- statement:
--   For any finite family of complex $n\times n$ matrices, $n\ge2$, and $i\ne j$:
--
--   1. If $m\ge1$, $\alpha_k>0$, $\sum_k\alpha_k=1$, and $U_k\in SU(n)$, then
--
--   $$\left(\sum_{k=1}^m\alpha_kL_{U_k}\right)_{ij}=0\quad\Longrightarrow\quad (L_{U_k})_{ij}=0\text{ for every }k.$$
--
--   2. If $(L_U)_{ij}=0$, then $(U^*V_kU)_{ij}=0$ for every jump $k$.
--
--   Only off-diagonal entries and strictly positive mixture components are covered.
-- source:
--   Reachability, Coolability, and Stabilizability of Open Markovian Quantum Systems with Fast Unitary Control, arXiv:2308.00561v1, PDF p. 29, Lemma B.1: Zeros cannot cancel in induced generators

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P16

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ENNReal NNReal Matrix.Norms.L2Operator

open MeasureTheory Filter

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance 100] LieRing.ofAssociativeRing

namespace QAlgorithms.Papers.Independent.Dependency50.P16

local notation "Mat" => fun n : ℕ => Matrix (Fin n) (Fin n) ℂ

local notation "Vec" => fun n : ℕ => Fin n → ℝ

local notation "Hilbert" => fun n : ℕ => EuclideanSpace ℂ (Fin n)

local notation "Operator" => fun n : ℕ => Module.End ℂ (Mat n)

/-- arXiv:2308.00561v1, PDF p.29, Lemma B.1: Zeros cannot cancel in induced generators. Lean induced is -L_U, so the displayed L_U entries are explicitly negated. Zero-weight components and diagonal entries are not included. -/
theorem inducedZeros_noCancellation {n r : ℕ} (hn : 2 ≤ n) (V : Fin r → Mat n)
    (i j : Fin n) (hij : i ≠ j) :
    (∀ (m : ℕ), 0 < m → ∀ (a : Fin m → ℝ) (U : Fin m → Mat n),
      (∀ k, 0 < a k) → (∑ k, a k) = 1 → (∀ k, specialUnitary (U k)) →
      (∑ k, a k * (-(populationGenerator V (U k) i j))) = 0 →
      ∀ k, -(populationGenerator V (U k) i j) = 0) ∧
    (∀ U : Mat n, specialUnitary U → -(populationGenerator V U i j) = 0 →
      ∀ k, (Uᴴ * V k * U) i j = 0) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P16

end
