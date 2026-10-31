-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P57_pretty_good_measurement_lower_bound
-- name    : QAlgorithms.Papers.Independent.Intake100.P57.pretty_good_measurement_lower_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:02:17.657372+00:00
-- url     : https://prove2.me/theorems/8cbbe41d-a211-4af1-a118-d659b1a0a357
-- title:
--   Pretty good measurement lower bound for a uniform mixed-state ensemble
-- statement:
--   Let $N\ge1$ and let $\eta_1,\ldots,\eta_N$ be density operators on a common nonempty finite-dimensional quantum register. Each label has prior probability $1/N$. Define the ensemble average and average rank by
--
--   $$
--   \bar\eta=\frac1N\sum_{i=1}^N\eta_i,
--   \qquad \bar r=\frac1N\sum_{i=1}^N\operatorname{rank}(\eta_i).
--   $$
--
--   For $S=\sum_i\eta_i$, the pretty good measurement has effects $E_i=S^{-1/2}\eta_iS^{-1/2}$ on the support of $S$. Zero eigenvalues of $S$ are assigned inverse zero, and any remaining identity on its orthogonal complement can be assigned to one outcome without changing the success probability. Its uniform average success satisfies
--
--   $$
--   p^{\mathrm{pgm}}_{\mathrm{succ}}=\frac1N\sum_i\operatorname{Tr}(E_i\eta_i)
--   \ge\frac1{N\bar r\,\operatorname{Tr}(\bar\eta^2)}.
--   $$
--
--   Normalization and $N>0$ make the denominator positive. This general bound applies in particular to the fixed-EPR-resource ensemble of Appendix A.3; no optimized resource state or nonuniform prior is introduced.
--
--   **Formalization Note** The accepted mixedPgmSuccess uses prior-weighted states and their mean inverse root. With uniform priors it is exactly the probability displayed above.
-- source:
--   Simplified instantaneous non-local quantum computation with applications to position-based cryptography, arXiv:1101.1065v3, PDF p. 16, A.3

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P57

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intake100.P57

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

-- P34 uses half the channel distance. Every occurrence below is multiplied by two.

open QAlgorithms.Papers.Independent.Information100.P34 (diamondDistance)

open QAlgorithms.Papers.Independent.Dependency50.P07 (ensembleMean)

/-- Lemma A.3, PDF p.16, with support-inverse convention on pp.16–17.
States are normalized, the ensemble is nonempty, and priors are exactly uniform.
The accepted mixedPgmSuccess uses the generalized inverse square root and gives
exactly (A5); completing the POVM off its support leaves this number unchanged. -/
theorem pretty_good_measurement_lower_bound {I : Type} [Fintype I]
    [DecidableEq I] [Nonempty I] (N : ℕ) (hN : 0 < N)
    (eta : Fin N → Matrix I I ℂ) (heta : ∀ i, IsDensityMatrix (eta i)) :
    1 / ((N : ℝ) * ensembleMeanRank eta * ((ensembleMean ⟨(fun _ : Fin N => (N : ℝ)⁻¹), eta⟩)^2).trace.re) ≤
      mixedPgmSuccess (fun _ : Fin N => (N : ℝ)⁻¹) eta := by sorry

end QAlgorithms.Papers.Independent.Intake100.P57

end
