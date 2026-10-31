-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P89_polynomial_rkhs
-- name    : QAlgorithms.Papers.Independent.Intake100.P89.polynomial_rkhs
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:42:40.551969+00:00
-- url     : https://prove2.me/theorems/78407a75-9a3c-436e-bb89-a862952d6527
-- title:
--   Example 4.2: Gaussian polynomial RKHS
-- statement:
--   Let $k\ge0$ be an integer, let $Z_0,\ldots,Z_k$ be iid standard normals, and set $X(t)=\sum_{i=0}^kZ_it^i/i!$ on $[0,1]$. Its RKHS is exactly the polynomials of degree at most $k$, written $P_a(t)=\sum_{i=0}^ka_it^i/i!$, with
--   $$\langle P_a,P_b\rangle_H=\sum_{i=0}^ka_ib_i,\qquad\|P_a\|_H^2=\sum_{i=0}^ka_i^2=\sum_{i=0}^k(P_a^{(i)}(0))^2.$$
--   For $k=0$ this is the variance-one constant process, and the zero polynomial is included.
-- source:
--   Reproducing kernel Hilbert spaces of Gaussian priors, arXiv:0805.3252v1, PDF p. 13, Example 4.2: Gaussian polynomial RKHS

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P89

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory

open scoped Topology BigOperators ENNReal

namespace QAlgorithms.Papers.Independent.Intake100.P89

universe u v w

variable {Omega : Type u} [MeasurableSpace Omega]

section PathResults

variable (P : Measure Omega) [hP : IsProbabilityMeasure P]

include hP

/-- Example 4.2: Gaussian polynomial RKHS, arXiv:0805.3252v1, PDF p.13.
Factorials are retained. The process function model equals the C[0,1] model by Theorem 2.1; derivatives are of the global polynomial, avoiding boundary derivative conventions. -/
theorem polynomial_rkhs
(k : ℕ) (Z : Fin (k + 1) → Omega → ℝ) (hZ : StandardNormals P Z) :
    let X := fun t : Time => fun o => polynomialReal k (fun i => Z i o) (t : ℝ)
    processRKHS P X = Set.range (fun a : Fin (k + 1) → ℝ =>
      fun t : Time => polynomialReal k a (t : ℝ)) ∧
    (∀ a b : Fin (k + 1) → ℝ,
      processInner P X (fun t => polynomialReal k a (t : ℝ))
        (fun t => polynomialReal k b (t : ℝ)) = ∑ i, a i * b i) ∧
    (∀ a : Fin (k + 1) → ℝ,
      processNorm P X (fun t => polynomialReal k a (t : ℝ)) ^ 2 = ∑ i, (a i) ^ 2) ∧
    ∀ (a : Fin (k + 1) → ℝ) (i : Fin (k + 1)),
      iteratedDeriv (i : ℕ) (polynomialReal k a) 0 = a i := by sorry

end PathResults

end QAlgorithms.Papers.Independent.Intake100.P89

end
