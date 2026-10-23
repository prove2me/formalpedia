-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P16_rateSums_spectralMajorization
-- name    : QAlgorithms.Papers.Independent.Dependency50.P16.rateSums_spectralMajorization
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T08:37:59.089921+00:00
-- url     : https://prove2.me/theorems/571e9a83-b720-4961-920c-985e5a06373b
-- title:
--   Lemma B.2: Row and column sums of J and their majorization bounds
-- statement:
--   For a finite jump family and any $U\in U(n)$, put $u_i=Ue_i$ and $J_{ij}(U)=\sum_k|(U^*V_kU)_{ij}|^2$. Define $A=\sum_kV_kV_k^*$, $B=\sum_kV_k^*V_k$, $C=A-B$, and $D=A+B$. Then
--
--   $$ (Je)_i=\langle u_i,Au_i\rangle,\quad(J^Te)_i=\langle u_i,Bu_i\rangle,\quad((J-J^T)e)_i=\langle u_i,Cu_i\rangle,\quad((J+J^T)e)_i=\langle u_i,Du_i\rangle.$$
--
--   All four majorization conclusions hold:
--
--   $$Je\prec\operatorname{spec}^{\downarrow}A,\quad J^Te\prec\operatorname{spec}^{\downarrow}B,\quad(J-J^T)e\prec\operatorname{spec}^{\downarrow}C,\quad(J+J^T)e\prec\operatorname{spec}^{\downarrow}D.$$
--
--   These Hermitian matrices need not have trace one. The identities and bounds describe both directional flow sums and their symmetric and antisymmetric parts.
-- source:
--   Reachability, Coolability, and Stabilizability of Open Markovian Quantum Systems with Fast Unitary Control, arXiv:2308.00561v1, PDF p. 29, Lemma B.2: Row and column sums of J and their majorization bounds

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

/-- arXiv:2308.00561v1, PDF p.29, Lemma B.2: Row and column sums of J and their majorization bounds. All four identities and all four majorizations are retained. Expectations use columns of U and real parts of Hermitian diagonal entries. U(n), not just SU(n), is quantified. -/
theorem rateSums_spectralMajorization {n r : ℕ} (hn : 2 ≤ n) (V : Fin r → Mat n)
    (U : Mat n) (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    (∀ i, ∑ j, rates V U i j = ((Uᴴ * (∑ k, V k * (V k)ᴴ) * U) i i).re) ∧
    (∀ i, ∑ j, rates V U j i = ((Uᴴ * (∑ k, (V k)ᴴ * V k) * U) i i).re) ∧
    (∀ i, (∑ j, rates V U i j) - (∑ j, rates V U j i) =
      ((Uᴴ * (∑ k, (V k * (V k)ᴴ - (V k)ᴴ * V k)) * U) i i).re) ∧
    (∀ i, (∑ j, rates V U i j) + (∑ j, rates V U j i) =
      ((Uᴴ * (∑ k, (V k * (V k)ᴴ + (V k)ᴴ * V k)) * U) i i).re) ∧
    spectrallyMajorizedBy (fun i => ∑ j, rates V U i j) (∑ k, V k * (V k)ᴴ) ∧
    spectrallyMajorizedBy (fun i => ∑ j, rates V U j i) (∑ k, (V k)ᴴ * V k) ∧
    spectrallyMajorizedBy (fun i => (∑ j, rates V U i j) - (∑ j, rates V U j i))
      (∑ k, (V k * (V k)ᴴ - (V k)ᴴ * V k)) ∧
    spectrallyMajorizedBy (fun i => (∑ j, rates V U i j) + (∑ j, rates V U j i))
      (∑ k, (V k * (V k)ᴴ + (V k)ᴴ * V k)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P16

end
