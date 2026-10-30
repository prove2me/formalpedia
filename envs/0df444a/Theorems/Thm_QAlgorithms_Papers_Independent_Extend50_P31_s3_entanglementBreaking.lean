-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_s3_entanglementBreaking
-- name    : QAlgorithms.Papers.Independent.Extend50.P31.s3_entanglementBreaking
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T23:01:41.501563+00:00
-- url     : https://prove2.me/theorems/de915bb6-cf13-4e54-9b7e-6e6515071564
-- title:
--   Section 8.5, Eqs.(153)–(154): S(3) entanglement-breaking region
-- statement:
--   For the concrete real-parameter epsilon family $\Phi_{s,t}$, being a CPTP entanglement-breaking channel is equivalent to
--
--   $$
--   \bigl[-1\le s\le0,\ |t|\le(1+s)/2\bigr]\ \lor\ \bigl[0<s\le1,\ |t|\le(1-s)/2\bigr].
--   $$
--
--   Within the CP triangle $-1\le s\le1$, $|t|\le(1+s)/2$, the unnormalized Choi matrix lies in the separable positive cone if and only if it is PPT, with additional inequalities $-1\le s\le1$ and $|t|\le(1-s)/2$. Equivalently $J/2$ is a separable density matrix. The frozen positive-cone EB predicate applies the channel to every bipartite density matrix with arbitrary positive finite ancilla dimension.
-- source:
--   Structure of irreducibly covariant quantum channels for finite groups, arXiv:1610.05657v2, PDF p. 31, Section 8.5, Eqs.(153)–(154): S(3) entanglement-breaking region

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P31

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Extend50.P31

open QAlgorithms.Papers.Independent.Information100.P44 (Mat matrixUnit)

open QAlgorithms.Papers.Independent.Frontier18.P17 (hs)

open QAlgorithms.Papers.Independent.Bridge50.P37 (hsAdjoint)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Dependency50.P26 (TracePreserving)

open QAlgorithms.Papers.Independent.Dependency50.P16 (sandwich)

open QAlgorithms.Papers.Independent.Information100.P75 (phase)

variable {G A : Type*} [Group G] [Fintype G] [Fintype A] [DecidableEq A] {n : ℕ}

/-- PDF pp.30--31 Eqs.(153),(154). The separable positive cone accommodates unnormalized J.
Outside the channel domain, PPT alone is not claimed to imply CP or EB. -/
theorem s3_entanglementBreaking (s t : ℝ) :
    ((IsPaperChannel (s3Map s t) ∧ QAlgorithms.Entanglement.IsEntanglementBreakingPositive (s3Map s t)) ↔
      ((-1 ≤ s ∧ s ≤ 0 ∧ |t| ≤ (1+s)/2) ∨ (0 < s ∧ s ≤ 1 ∧ |t| ≤ (1-s)/2))) ∧
    (S3CP s t →
      (QAlgorithms.Entanglement.IsSeparablePositive (choi (s3Map s t)) ↔
        (QAlgorithms.Entanglement.partialTransposeFirst (choi (s3Map s t))).PosSemidef) ∧
      ((QAlgorithms.Entanglement.partialTransposeFirst (choi (s3Map s t))).PosSemidef ↔
        -1 ≤ s ∧ s ≤ 1 ∧ |t| ≤ (1-s)/2)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P31

end
