-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P84_goldenThompsonTraceFamily
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P84.goldenThompsonTraceFamily
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:10:11.512519+00:00
-- url     : https://prove2.me/theorems/aacde534-876d-4129-ac86-79377cc51b7c
-- title:
--   Section 4, printed 3.1: trace-exponential family (13)
-- statement:
--   For self-adjoint $A,B$ define, for $p>0$,
--
--   $$F(p)=\operatorname{Tr}\left(e^{pB/2}e^{pA}e^{pB/2}\right)^{1/p}.$$
--
--   Then $F$ is nondecreasing on $(0,\infty)$ and $\lim_{p\downarrow0}F(p)=\operatorname{Tr}e^{A+B}$. It is constant on $(0,\infty)$ iff $AB=BA$, and is strictly increasing otherwise. All matrix powers use the positive spectral calculus; the value at zero is unused.
-- source:
--   Monotonicity of quantum relative entropy revisited, arXiv:quant-ph/0209053v1, PDF p. 6, Section 4, printed 3.1: trace-exponential family (13)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P84

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P84

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

-- Pinned accepted definitions, inspected at their recorded source locations.

open QAlgorithms.Papers.Independent.Renew46.P35 (traceAdjoint)

open QAlgorithms.Papers.Independent.Dependency50.P21 (imaginaryPower marginalAB)

/-- Petz, arXiv:quant-ph/0209053v1, PDF p.6, (13) [5,7].
The constructed positive-p family is increasing, has the stated right limit at zero,
and is constant exactly for commuting A,B, otherwise strictly increasing.
The value of the total function at p=0 is unused. -/
theorem goldenThompsonTraceFamily {I : Type*} [Fintype I]
    (A B : Matrix I I ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    let F : ℝ → ℝ := fun p =>
      (cfc (fun x : ℝ => Real.rpow x (1 / p))
        (NormedSpace.exp (((p / 2 : ℝ) : ℂ) • B) *
          NormedSpace.exp ((p : ℂ) • A) *
          NormedSpace.exp (((p / 2 : ℝ) : ℂ) • B))).trace.re
    MonotoneOn F (Set.Ioi 0) ∧
    Filter.Tendsto F (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((NormedSpace.exp (A + B)).trace.re)) ∧
    ((∀ p : ℝ, 0 < p → ∀ q : ℝ, 0 < q → F p = F q) ↔ Commute A B) ∧
    (¬Commute A B → StrictMonoOn F (Set.Ioi 0)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P84

end
