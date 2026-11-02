-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P97_expanded_entropy
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P97.expanded_entropy
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:44:28.98391+00:00
-- url     : https://prove2.me/theorems/29bcf1f0-5e0c-45eb-b1c6-8b2d6855b6fa
-- title:
--   Theorem 1 prime: expanded entropy reformulation
-- statement:
--   Let $\rho_{ABCD}$ be a positive semidefinite complex density matrix of trace one on four finite-dimensional tensor factors $A,B,C,D$, each of positive dimension (dimension one is allowed). Every $S(X)$ is the base-two von Neumann entropy of the actual $X$ marginal of this same state, with $0\log_2 0=0$. For disjoint groups write $S(X\mid Y)=S(XY)-S(Y)$, $I(X;Y)=S(X)+S(Y)-S(XY)$, and $I(X;Z\mid Y)=S(XY)+S(YZ)-S(XYZ)-S(Y)$. Assume
--
--   $$
--   \begin{aligned}
--   S(AB)+S(BC)-S(B)-S(ABC)&=0,\
--   S(CA)+S(AB)-S(A)-S(CAB)&=0,\
--   S(AD)+S(DB)-S(D)-S(ADB)&=0.
--   \end{aligned}
--   $$
--
--   Then
--
--   $$
--   S(ABC)+S(D)\ge S(AB)+S(CD),\qquad I(ABC;D)\ge I(AB;CD).
--   $$
--
--   The two conclusions express the same entropy inequality after cancellation. All reordered subsystem labels denote the same tensor factors.
-- source:
--   A new inequality for the von Neumann entropy, arXiv:quant-ph/0406162v1, PDF p. 6, Theorem 1 prime

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P97

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P97

attribute [local instance] Classical.propDecidable Classical.decEq

local notation "A" => ({0} : Finset (Fin 4))

local notation "B" => ({1} : Finset (Fin 4))

local notation "C" => ({2} : Finset (Fin 4))

local notation "D" => ({3} : Finset (Fin 4))

/-- PDF p.6, Theorem 1 prime: expanded entropy and mutual-information forms.
Subsystem permutations are unions of the same factors, and no purity is assumed. -/
theorem expanded_entropy (q : FourPartyState)
    (hABC : fourPartyEntropyBits q (A ∪ B) + fourPartyEntropyBits q (B ∪ C) - fourPartyEntropyBits q B - fourPartyEntropyBits q (A ∪ B ∪ C) = 0)
    (hCAB : fourPartyEntropyBits q (C ∪ A) + fourPartyEntropyBits q (A ∪ B) - fourPartyEntropyBits q A - fourPartyEntropyBits q (C ∪ A ∪ B) = 0)
    (hADB : fourPartyEntropyBits q (A ∪ D) + fourPartyEntropyBits q (D ∪ B) - fourPartyEntropyBits q D - fourPartyEntropyBits q (A ∪ D ∪ B) = 0) :
    fourPartyEntropyBits q (A ∪ B) + fourPartyEntropyBits q (C ∪ D) ≤ fourPartyEntropyBits q (A ∪ B ∪ C) + fourPartyEntropyBits q D ∧
    mutualValue (fourPartyEntropyBits q) (A ∪ B) (C ∪ D) ≤ mutualValue (fourPartyEntropyBits q) (A ∪ B ∪ C) D := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P97

end
