-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P30_wh_two_number
-- name    : QAlgorithms.Papers.Independent.Renew46.P30.wh_two_number
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:20:28.492991+00:00
-- url     : https://prove2.me/theorems/fde7e377-035b-4b64-be1a-8213f61377a2
-- title:
--   §V.B.2(ii): two equal number inputs
-- statement:
--   Let $n>0$ and let the full two-mode input be $|n,n\rangle$ under identical Weyl displacements. With likelihood measured relative to $d^2z/\pi$, the exact optimum is
--
--   $$L_{\max}=2\left(\sum_{k=0}^n\frac{\binom nk\sqrt{(2k)!(2n-2k)!}}{2^n n!}\right)^2.$$
--
--   The explicit full-space seed is the number-product completion for $N=2$. It is positive, gives a weakly normalized operator measure, and attains the universal bound, including regular generalized competitors. The observed numerical behavior for $n\le1000$ is not promoted to an asymptotic theorem.
-- source:
--   Covariant quantum measurements which maximize the likelihood, arXiv:quant-ph/0403083v1, PDF p. 6, §V.B.2(ii): two equal number inputs

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P30

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P30

open MeasureTheory

open QAlgorithms.Papers.Independent.Dependency50.P39 (IsTraceClass)

open QAlgorithms.Papers.Independent.Claimed50.P14 (SU)

open QAlgorithms.Papers.Independent.Claimed50.P17 (pairAction)

open scoped ComplexConjugate ComplexOrder Manifold ContDiff ENNReal Matrix Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]

variable (R : CovariantHilbertData G H)

variable {M : Type*} [DecidableEq M]

variable (D : Components R M)

open QAlgorithms.Papers.Independent.Dependency50.P39
  (Fock FockOperator fockKet displacement displacementMatrix coherentMeasure coherentKet)

variable {J : Type*} [DecidableEq J]

/-- PDF p.6, §V.B.2(ii): exact two-number-input optimum with explicit full-space attainment. -/
theorem wh_two_number (n : ℕ) (hn : 0 < n) :
    MultiMaximum (multiKet (fun _ : Fin 2 => n)) (numberSeed 1 (fun _ => n))
      (equalNumberFormula n) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P30

end
