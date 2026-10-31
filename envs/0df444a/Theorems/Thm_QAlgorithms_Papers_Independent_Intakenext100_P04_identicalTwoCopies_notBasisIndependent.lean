-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P04_identicalTwoCopies_notBasisIndependent
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P04.identicalTwoCopies_notBasisIndependent
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T03:52:03.707173+00:00
-- url     : https://prove2.me/theorems/173f6b07-c821-4b74-b5d4-346f04a61f1c
-- title:
--   An identical two-copy BB84 component violates weighted basis independence
-- statement:
--   Write $|\psi_{0,g}\rangle=|g\rangle_Z$ and $|\psi_{1,g}\rangle=H|g\rangle_Z$ for the standard BB84 qubit. For unbiased basis and bit labels, the full two-copy states $\rho_{a,g}=|\psi_{a,g}\rangle\langle\psi_{a,g}|^{\otimes2}$ are normalized density operators but satisfy
--
--   $$
--   \tfrac14\sum_g\rho_{0,g}\ne\tfrac14\sum_g\rho_{1,g}.
--   $$
--
--   More generally, for every $0<t\le1$, consider the physical state on the direct sum of the one-copy and two-copy sectors
--
--   $$
--   \sigma_{a,g}=(1-t)|\psi_{a,g}\rangle\langle\psi_{a,g}|\ \oplus\ t\rho_{a,g}.
--   $$
--
--   Each $\sigma_{a,g}$ is a density operator and its two weighted basis averages are unequal. Thus even an arbitrarily rare positive identical-copy component defeats Eq.(1) when the full emitted system, including Eve's copy, is retained. This is an exclusion from this paper's proof, not a security impossibility theorem and not a claim about all entanglement-based multipair sources.
-- source:
--   Secure quantum key distribution with an uncharacterized source, arXiv:quant-ph/0208155v2, PDF p. 4, Paragraph on the defective identical-copy source

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P04

noncomputable section

universe u v w

namespace QAlgorithms.Papers.Independent.Intakenext100.P04

open QAlgorithms

open QAlgorithms.Papers.Independent.Dependency50.P13
  (State IsTraceClass IsPositive operatorTrace)

open QAlgorithms.Papers.Independent.Advance50.P18 (keyEntropy)

open scoped ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Koashi–Preskill PDF p.4, paragraph on the source emitting two identical
copies: the full emitted source fails Eq.(1), including an arbitrarily rare
positive two-copy component. This excludes this source from the proof; it
makes no claim about general multipair entanglement sources. -/
theorem identicalTwoCopies_notBasisIndependent :
    (∀ a g, IsDensityMatrix (identicalCopyState a g)) ∧
    copiedBasisAverage false ≠ copiedBasisAverage true ∧
    ∀ t : ℝ, 0 < t → t ≤ 1 →
      (∀ a g, IsDensityMatrix (occasionalCopyState t a g)) ∧
      occasionalCopyAverage t false ≠ occasionalCopyAverage t true := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P04

end
