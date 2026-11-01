-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P51_liebConcavity
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P51.liebConcavity
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:44:16.032669+00:00
-- url     : https://prove2.me/theorems/a1a0582e-ad3d-4b6e-a593-15ffbeb87569
-- title:
--   Theorem 2: Lieb concavity of trace exp(K+log A)
-- statement:
--   Fix a self-adjoint matrix $K$ and write $F_K(A)=\operatorname{Tr}\exp(K+\log A)$ for positive definite $A$. For positive definite $A,B$ and $0\le t\le1$,
--   $$tF_K(A)+(1-t)F_K(B)\le F_K(tA+(1-t)B).$$
--   The matrices need not be normalized. This is non-strict concavity on the entire positive definite cone.
-- source:
--   Inequalities for Quantum Entropy: A Review with Conditions for Equality, arXiv:quant-ph/0205064v2, PDF p. 5, Theorem 2: Lieb concavity of trace exp(K+log A)

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

/-- Theorem 2, PDF p.5: non-strict Lieb concavity for arbitrary positive definite matrices. -/
theorem liebConcavity [Nonempty A] (L X Y : Mat A) (hL : L.IsHermitian) (hX : X.PosDef) (hY : Y.PosDef)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t * (NormedSpace.exp (L + logMatrix X)).trace.re +
      (1 - t) * (NormedSpace.exp (L + logMatrix Y)).trace.re ≤
    (NormedSpace.exp (L + logMatrix ((t : ℂ) • X + ((1 - t : ℝ) : ℂ) • Y))).trace.re := by sorry

end Statements

end QAlgorithms.Papers.Independent.Intakethird100.P51

end
