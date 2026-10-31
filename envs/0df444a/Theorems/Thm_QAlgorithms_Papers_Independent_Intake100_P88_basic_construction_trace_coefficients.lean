-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P88_basic_construction_trace_coefficients
-- name    : QAlgorithms.Papers.Independent.Intake100.P88.basic_construction_trace_coefficients
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:40:57.022077+00:00
-- url     : https://prove2.me/theorems/e16c0855-0776-4e96-a786-59e841cde469
-- title:
--   Theorem 4.28(c): trace-coefficient ratio
-- statement:
--   Let $F$ be algebraically closed and let $A\subseteq B$ be finite-dimensional split semisimple unital $F$-algebras with compatible matrix units. Let $\epsilon:B\to A$ be $A$-bimodule linear, and let traces have expansions $t_A=\sum_\mu c_A^\mu\chi_A^\mu$ and $t_B=\sum_\lambda c_B^\lambda\chi_B^\lambda$, with $t_A\circ\epsilon=t_B$. Fix a branching edge copy $\mu\to\lambda$ and its compatible coordinate inclusion $j$. If $E^A_{pp}$ and $E^B_{j(p),j(p)}$ are the corresponding diagonal matrix units, define $\epsilon_\mu^\lambda$ by extracting its $00$ matrix coefficient from $\epsilon(E^B_{j(0),j(0)})$. Then
--
--   $$\epsilon(E^B_{j(p),j(p)})=\epsilon_\mu^\lambda E^A_{pp}\quad\text{for every }p,\qquad
--   c_B^\lambda=\epsilon_\mu^\lambda c_A^\mu.$$
--
--   Repeated branching copies are separate choices of $j$. This formulation retains zero trace coefficients and requires no division by them.
-- source:
--   Partition Algebras, arXiv:math/0401314v2, PDF p. 37, Theorem 4.28(c): trace-coefficient ratio

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P88

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P88

attribute [local instance] Classical.propDecidable

open scoped BigOperators Matrix

open QAlgorithms.Papers.Independent.Information100.P65 (hookLength)

open QAlgorithms.Papers.Independent.Renew46.P30 (TensorIndex)

universe u v w x y

/-- Trace coefficient identity without division, PDF pp.36--38, Theorem 4.28(c).
The two edge-matrix equations are precisely compatibility of the chosen row and column
matrix units for one branching copy. Repeated edges remain separate choices of `j`.
The scalar is extracted from the actual bimodule map, not independently supplied. -/
theorem basic_construction_trace_coefficients (F A B I J : Type*)
    [Field F] [IsAlgClosed F] [Ring A] [Algebra F A] [FiniteDimensional F A]
    [Ring B] [Algebra F B] [FiniteDimensional F B]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (da : I → ℕ) (db : J → ℕ) (ha : ∀ i, 0 < da i) (_hb : ∀ j, 0 < db j)
    (ea : A ≃ₐ[F] ((i : I) → Matrix (Fin (da i)) (Fin (da i)) F))
    (eb : B ≃ₐ[F] ((j : J) → Matrix (Fin (db j)) (Fin (db j)) F))
    (inc : A →ₐ[F] B) (_hinj : Function.Injective inc) (eps : B →ₗ[F] A)
    (_hleft : ∀ a b, eps (inc a * b) = a * eps b)
    (_hright : ∀ a b, eps (b * inc a) = eps b * a)
    (ca : I → F) (cb : J → F)
    (_htrace : ∀ b, splitTrace da ea ca (eps b) = splitTrace db eb cb b)
    (mu : I) (lam : J) (j : Fin (da mu) ↪ Fin (db lam))
    (_hcolumn : ∀ a, eb (inc a) lam * edgeMatrix (F := F) j = edgeMatrix j * ea a mu)
    (_hrow : ∀ a, (edgeMatrix (F := F) j).transpose * eb (inc a) lam =
      ea a mu * (edgeMatrix j).transpose) :
    let p : Fin (da mu) := ⟨0, ha mu⟩
    let scalar : F := ea (eps (splitMatrixUnit db eb lam (j p) (j p))) mu p p
    (∀ q : Fin (da mu), eps (splitMatrixUnit db eb lam (j q) (j q)) =
      scalar • splitMatrixUnit da ea mu q q) ∧ cb lam = scalar * ca mu := by sorry

end QAlgorithms.Papers.Independent.Intake100.P88

end
