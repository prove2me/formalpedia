-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P97_purification_variants
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P97.purification_variants
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:45:19.488181+00:00
-- url     : https://prove2.me/theorems/d91e63b4-1e40-4993-8e71-64ad4dcf16b8
-- title:
--   Theorem 1 double prime: all three purification variants
-- statement:
--   Let $\rho_{ABCD}$ be a positive semidefinite complex density matrix of trace one on four finite-dimensional tensor factors $A,B,C,D$, each of positive dimension (dimension one is allowed). Every $S(X)$ is the base-two von Neumann entropy of the actual $X$ marginal of this same state, with $0\log_2 0=0$. For disjoint groups write $S(X\mid Y)=S(XY)-S(Y)$, $I(X;Y)=S(X)+S(Y)-S(XY)$, and $I(X;Z\mid Y)=S(XY)+S(YZ)-S(XYZ)-S(Y)$. Each of the following is a separate implication for this state:
--
--   1. If $I(A;C\mid B)=I(B;C\mid A)=I(A;B\mid CD)=0$, then
--
--   $$
--   S(C\mid AB)+S(C\mid ABD)\ge0.
--   $$
--
--   2. If $S(C\mid A)+S(C\mid BD)=0$, $I(A;C\mid BD)=0$, and $S(A\mid D)+S(A\mid BC)=0$, then
--
--   $$
--   S(C\mid D)+S(C\mid BD)\le0.
--   $$
--
--   3. If $S(B\mid A)+S(B\mid CD)=0$, $S(A\mid B)+S(A\mid CD)=0$, and $I(A;B\mid D)=0$, then
--
--   $$
--   S(D)+S(CD)\ge S(AB)+S(ABC).
--   $$
--
--   These are the three purification reformulations of the constrained inequality; no purity assumption is imposed on $\rho_{ABCD}$.
-- source:
--   A new inequality for the von Neumann entropy, arXiv:quant-ph/0406162v1, PDF p. 6, Theorem 1 double prime

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P97

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P97

attribute [local instance] Classical.propDecidable Classical.decEq

local notation "A" => ({0} : Finset (Fin 4))

local notation "B" => ({1} : Finset (Fin 4))

local notation "C" => ({2} : Finset (Fin 4))

local notation "D" => ({3} : Finset (Fin 4))

/-- PDF pp.6–7, Theorem 1 double prime: three separate implications, each with
its own three zero expressions. The purifying E in the proof is not input data.
Case (1) retains C|ABD; the inequality in case (2) is ≤. -/
theorem purification_variants (q : FourPartyState) :
    ((conditionalMutualValue (fourPartyEntropyBits q) A C B = 0 ∧ conditionalMutualValue (fourPartyEntropyBits q) B C A = 0 ∧
      conditionalMutualValue (fourPartyEntropyBits q) A B (C ∪ D) = 0) →
      0 ≤ entropyDifference (fourPartyEntropyBits q) C (A ∪ B) + entropyDifference (fourPartyEntropyBits q) C (A ∪ B ∪ D)) ∧
    ((entropyDifference (fourPartyEntropyBits q) C A + entropyDifference (fourPartyEntropyBits q) C (B ∪ D) = 0 ∧
      conditionalMutualValue (fourPartyEntropyBits q) A C (B ∪ D) = 0 ∧
      entropyDifference (fourPartyEntropyBits q) A D + entropyDifference (fourPartyEntropyBits q) A (B ∪ C) = 0) →
      entropyDifference (fourPartyEntropyBits q) C D + entropyDifference (fourPartyEntropyBits q) C (B ∪ D) ≤ 0) ∧
    ((entropyDifference (fourPartyEntropyBits q) B A + entropyDifference (fourPartyEntropyBits q) B (C ∪ D) = 0 ∧
      entropyDifference (fourPartyEntropyBits q) A B + entropyDifference (fourPartyEntropyBits q) A (C ∪ D) = 0 ∧
      conditionalMutualValue (fourPartyEntropyBits q) A B D = 0) →
      fourPartyEntropyBits q (A ∪ B) + fourPartyEntropyBits q (A ∪ B ∪ C) ≤ fourPartyEntropyBits q D + fourPartyEntropyBits q (C ∪ D)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P97

end
