-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P51_partialTraceMonotonicity
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P51.partialTraceMonotonicity
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:55:58.410876+00:00
-- url     : https://prove2.me/theorems/a2160c46-24f0-4454-bedc-25ccf0ed7f4b
-- title:
--   Theorem 6: monotonicity under partial trace and corrected equality
-- statement:
--   Let $\rho_{12},\gamma_{12}>0$ have equal trace, without requiring trace one. Put $\rho_2=\operatorname{Tr}_1\rho_{12}$ and $\gamma_2=\operatorname{Tr}_1\gamma_{12}$. Then
--   $$H(\rho_2,\gamma_2)\le H(\rho_{12},\gamma_{12}),$$
--   with equality if and only if
--   $$\log\rho_{12}-\log\gamma_{12}=I_1\otimes(\log\rho_2-\log\gamma_2).$$
--   This is the proof-forced correction of the conflicting signs printed after Theorem 6, and agrees with equation (40). The correction requires independent moderation.
-- source:
--   Inequalities for Quantum Entropy: A Review with Conditions for Equality, arXiv:quant-ph/0205064v2, PDF p. 13, Theorem 6: monotonicity under partial trace and corrected equality

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P51

noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Intakethird100.P51

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact interfaces from the frozen accepted library; no local redeclarations.

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy holevo IsLaw)

open QAlgorithms.Papers.Independent.Information100.P27 (average)

open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy marginalAB channelAdjoint)

open QAlgorithms.Papers.Independent.Dependency50.P35 (marginalAC)

open QAlgorithms.Papers.Independent.Gap48.P19 (shannonNats)

open QAlgorithms.Papers.Independent.Gap48.P33 (measurementInformation)

section Statements

variable {A B C D J K O : Type}

variable [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype J] [Fintype K] [Fintype O]

variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

variable [DecidableEq J] [DecidableEq K] [DecidableEq O]

/-- Theorem 6, PDF p.13, CORRECTED SOURCE SIGN: the printed equality condition
has both a plus-sign version and a reversed difference. The proof's
log B = log gamma12 - log gamma2 + log rho2 forces the difference below,
consistent with (40). No normalization or equal-trace condition is omitted. -/
theorem partialTraceMonotonicity [Nonempty A] [Nonempty B] (rho gamma : Mat (A × B))
    (hr : rho.PosDef) (hg : gamma.PosDef) (ht : rho.trace = gamma.trace) :
    (relativeEntropy (traceLeft rho) (traceLeft gamma)).toReal ≤ (relativeEntropy rho gamma).toReal ∧
      ((relativeEntropy (traceLeft rho) (traceLeft gamma)).toReal = (relativeEntropy rho gamma).toReal ↔
        logMatrix rho - logMatrix gamma =
          Matrix.kronecker (1 : Mat A) (logMatrix (traceLeft rho) - logMatrix (traceLeft gamma))) := by sorry

end Statements

end QAlgorithms.Papers.Independent.Intakethird100.P51

end
