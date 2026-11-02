-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P30_repetitionLimit
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P30.repetitionLimit
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:42:45.694582+00:00
-- url     : https://prove2.me/theorems/8910eba0-7ce3-4457-9bf0-8f3fe12c151a
-- title:
--   III A: monotone repetition thresholds and Chau limit, (10)
-- statement:
--   For $n\ge1$, let $q_n=Q_{R_n}^*$ denote the Bob-only repetition-code threshold. Set $r_n=(1/4)^{1/n}$, $a_n=4r_n+1$, and
--
--   $$\widetilde q_n=\frac{a_n-\sqrt{a_n^2-4r_na_n}}{2a_n},
--   \qquad c=\frac{5-\sqrt5}{10}.$$
--
--   The sequence $(q_n)_{n\ge1}$ is nondecreasing, and
--
--   $$\lim_{n\to\infty}\widetilde q_n=c,\qquad
--   \lim_{n\to\infty}(q_n-\widetilde q_n)=0,\qquad
--   \lim_{n\to\infty}q_n=c,\qquad q_n\le c.$$
--
--   No convergence rate is asserted. Positive block length is essential for the reciprocal exponent; the formal sequence is indexed by $n=k+1$. This establishes that finite repetition codes approach Chau's threshold.
-- source:
--   Numerical evidence for bound secrecy from two-way post-processing in quantum key distribution, arXiv:1612.07734v2, PDF p. 5, III A: monotone repetition thresholds and Chau limit, (10)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P30

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P30

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I J K L A B : Type}

variable [Fintype I] [Fintype J] [Fintype K] [Fintype L]

variable [Fintype A] [Fintype B]

/-- PDF p.5, (10): monotone positive-length thresholds, the explicit approximation,
its limit, and the Chau limit. No convergence rate is asserted. -/
theorem repetitionLimit :
    Monotone (fun k : ℕ => bobThreshold (repetition (Fin (k + 1)))) ∧
    Filter.Tendsto (fun k : ℕ => repetitionApprox (k + 1)) Filter.atTop (nhds chau) ∧
    Filter.Tendsto (fun k : ℕ => bobThreshold (repetition (Fin (k + 1))) -
      repetitionApprox (k + 1)) Filter.atTop (nhds 0) ∧
    Filter.Tendsto (fun k : ℕ => bobThreshold (repetition (Fin (k + 1))))
      Filter.atTop (nhds chau) ∧
    (∀ n : ℕ, 1 ≤ n → bobThreshold (repetition (Fin n)) ≤ chau) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P30

end
