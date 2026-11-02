-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P30_sdpCharacterization
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P30.sdpCharacterization
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:43:14.998471+00:00
-- url     : https://prove2.me/theorems/9014c400-5b16-4a8f-8814-32ca6070b69d
-- title:
--   III B: attained SDP optimum detects extendability, (11)–(12)
-- statement:
--   Let $A,B$ be finite nonempty systems and let $P\succeq0$ be any operator on $A\otimes B$, without a trace-one assumption. Identify $B'$ with a copy of $B$. Consider
--
--   $$t_{\min}(P)=\min\{t\in\mathbb R:\ \exists R=R^\dagger,
--   \ R+tI\succeq0,\ \operatorname{Tr}_{B'}R=P,
--   \ \operatorname{Tr}_{B}R=P\}.$$
--
--   Both marginal constraints use their actual coefficient partial traces and the stated register identification. The feasible objective set is nonempty and bounded below, and its finite infimum is attained. Moreover,
--
--   $$\mathrm{Ext}_B(P)\Longleftrightarrow t_{\min}(P)\le0,
--   \qquad \neg\mathrm{Ext}_B(P)\Longleftrightarrow t_{\min}(P)>0.$$
--
--   Whenever the optimum is nonpositive, every minimizing $R$ is a positive symmetric extension. The optimization variable $R$ is initially only Hermitian; requiring it positive in the feasible set would change the SDP. The zero operator is included.
-- source:
--   Numerical evidence for bound secrecy from two-way post-processing in quantum key distribution, arXiv:1612.07734v2, PDF p. 5, III B: attained SDP optimum detects extendability, (11)–(12)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P30

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P30

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I J K L A B : Type}

variable [Fintype I] [Fintype J] [Fintype K] [Fintype L]

variable [Fintype A] [Fintype B]

/-- PDF p.5, (11)–(12): finite attained SDP optimum detects extendability.
All finite nonempty systems and all PSD P, including zero, are covered. -/
theorem sdpCharacterization [Nonempty A] [Nonempty B]
    (P : Matrix (A × B) (A × B) ℂ) (hP : P.PosSemidef) :
    (slackValues P).Nonempty ∧ BddBelow (slackValues P) ∧
    (∃ R, SDPFeasible P (sdpMinimum P) R) ∧
    (BobExtendible P ↔ sdpMinimum P ≤ 0) ∧
    (¬ BobExtendible P ↔ 0 < sdpMinimum P) ∧
    (∀ R, SDPFeasible P (sdpMinimum P) R → sdpMinimum P ≤ 0 → IsBobCopyExtension P R) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P30

end
