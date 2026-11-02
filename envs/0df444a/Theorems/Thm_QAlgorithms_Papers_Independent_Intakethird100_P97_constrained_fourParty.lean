-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P97_constrained_fourParty
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P97.constrained_fourParty
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:37:19.833889+00:00
-- url     : https://prove2.me/theorems/2d6faa34-b00f-4408-b48e-3343d0817351
-- title:
--   Theorem 1: the new constrained four-party entropy inequality
-- statement:
--   Let $\rho_{ABCD}$ be a positive semidefinite complex density matrix of trace one on four finite-dimensional tensor factors $A,B,C,D$, each of positive dimension (dimension one is allowed). Every $S(X)$ is the base-two von Neumann entropy of the actual $X$ marginal of this same state, with $0\log_2 0=0$. For disjoint groups write $S(X\mid Y)=S(XY)-S(Y)$, $I(X;Y)=S(X)+S(Y)-S(XY)$, and $I(X;Z\mid Y)=S(XY)+S(YZ)-S(XYZ)-S(Y)$. If $I(A;C\mid B)=I(B;C\mid A)=I(A;B\mid D)=0$, then
--
--   $$
--   I(C;D)\ge I(C;AB).
--   $$
--
--   This bounds the correlation of $C$ with $AB$ by its correlation with $D$ under the three specified SSA equalities.
-- source:
--   A new inequality for the von Neumann entropy, arXiv:quant-ph/0406162v1, PDF p. 3, Theorem 1

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P97

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P97

attribute [local instance] Classical.propDecidable Classical.decEq

local notation "A" => ({0} : Finset (Fin 4))

local notation "B" => ({1} : Finset (Fin 4))

local notation "C" => ({2} : Finset (Fin 4))

local notation "D" => ({3} : Finset (Fin 4))

/-- PDF p.3, Theorem 1 (proof pp.3–5): the constrained four-party inequality. -/
theorem constrained_fourParty (q : FourPartyState) (hc : Constraints (fourPartyEntropyBits q)) :
    mutualValue (fourPartyEntropyBits q) C (A ∪ B) ≤ mutualValue (fourPartyEntropyBits q) C D := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P97

end
