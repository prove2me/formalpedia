-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P97_strict_and_tight_examples
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P97.strict_and_tight_examples
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:38:02.292755+00:00
-- url     : https://prove2.me/theorems/b746da35-67ff-4211-9b78-eccc44d3e117
-- title:
--   Remark 3: strict and tight examples exist
-- statement:
--   Let $\rho_{ABCD}$ be a positive semidefinite complex density matrix of trace one on four finite-dimensional tensor factors $A,B,C,D$, each of positive dimension (dimension one is allowed). Every $S(X)$ is the base-two von Neumann entropy of the actual $X$ marginal of this same state, with $0\log_2 0=0$. For disjoint groups write $S(X\mid Y)=S(XY)-S(Y)$, $I(X;Y)=S(X)+S(Y)-S(XY)$, and $I(X;Z\mid Y)=S(XY)+S(YZ)-S(XYZ)-S(Y)$. There exists a state obeying $I(A;C\mid B)=I(B;C\mid A)=I(A;B\mid D)=0$ for which the inequality is strict, and there exists a state obeying the same constraints for which it is tight:
--
--   $$
--   \exists\rho:\ I(C;D)>I(C;AB),\qquad \exists\sigma:\ I(C;D)=I(C;AB).
--   $$
--
--   The two existential states may use different finite local dimensions. This demonstrates both behaviors within the constrained class.
-- source:
--   A new inequality for the von Neumann entropy, arXiv:quant-ph/0406162v1, PDF p. 5, Remark 3

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P97

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P97

attribute [local instance] Classical.propDecidable Classical.decEq

local notation "A" => ({0} : Finset (Fin 4))

local notation "B" => ({1} : Finset (Fin 4))

local notation "C" => ({2} : Finset (Fin 4))

local notation "D" => ({3} : Finset (Fin 4))

/-- PDF p.5, Remark 3: both strictness and equality occur among states obeying
all three constraints. The witnesses may have different finite local dimensions. -/
theorem strict_and_tight_examples :
    (∃ q : FourPartyState, Constraints (fourPartyEntropyBits q) ∧
      mutualValue (fourPartyEntropyBits q) C (A ∪ B) < mutualValue (fourPartyEntropyBits q) C D) ∧
    (∃ q : FourPartyState, Constraints (fourPartyEntropyBits q) ∧
      mutualValue (fourPartyEntropyBits q) C (A ∪ B) = mutualValue (fourPartyEntropyBits q) C D) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P97

end
