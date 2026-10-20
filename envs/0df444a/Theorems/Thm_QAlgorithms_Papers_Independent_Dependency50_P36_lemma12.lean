-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P36_lemma12
-- name    : QAlgorithms.Papers.Independent.Dependency50.P36.lemma12
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T16:44:42.233662+00:00
-- url     : https://prove2.me/theorems/b4ab0397-ced6-4ac6-ac7f-e097206d84e3
-- title:
--   Semidefinite representation of PPT-prime
-- statement:
--   Let $A,B$ be nonzero finite-dimensional complex Hilbert spaces with fixed product bases, and let $\sigma$ be any operator on $A\otimes B$. With $T_B$ denoting Bob's partial transpose and $\|\cdot\|_1$ the trace norm,
--
--   $$\sigma\in\mathrm{PPT}'\ \Longleftrightarrow\ \sigma\ge0\ \text{and}\ \exists\sigma_+,\sigma_-\ge0:\ \sigma^{T_B}=\sigma_+-\sigma_-,\quad\operatorname{Tr}(\sigma_++\sigma_-)\le1,$$
--
--   where $\mathrm{PPT}'=\{\tau\ge0:\|\tau^{T_B}\|_1\le1\}$. No trace-one or orthogonality conditions are imposed on the auxiliary operators, and $\sigma=0$ is included. This converts the trace-norm constraint into semidefinite conditions.
-- source:
--   Non-asymptotic entanglement distillation, arXiv:1706.06221v3, PDF p. 19, Lemma 12: semidefinite representation of PPT-prime

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P36

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Dependency50.P36

open QAlgorithms.Papers.Independent.Information100.P03 (partialTransposeB)

open QAlgorithms.Papers.Independent.Information100.P04 (copies)

open QAlgorithms.Papers.Independent.Information100.P21 (FiniteLOCC)

open QAlgorithms.Papers.Independent.Information100.P34 (dephasing)

open QAlgorithms.Papers.Independent.Information100.P63 (testingBeta normalCDF normalQuantile)

open QAlgorithms.Papers.Independent.Information100.P80 (log2)

/-- Lemma 12, arXiv:1706.06221v3, PDF p.19: semidefinite representation of PPT-prime.
Auxiliary positive operators need not have orthogonal support or trace one. -/
theorem lemma12 {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]
    (sigma : Matrix (A × B) (A × B) ℂ) :
    pptPrime sigma ↔ sigma.PosSemidef ∧
      ∃ plus minus : Matrix (A × B) (A × B) ℂ,
        plus.PosSemidef ∧ minus.PosSemidef ∧ partialTransposeB sigma = plus - minus ∧
        (plus + minus).trace.re ≤ 1 := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P36

end
