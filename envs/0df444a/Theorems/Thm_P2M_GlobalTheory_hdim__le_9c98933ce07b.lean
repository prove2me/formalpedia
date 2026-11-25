-- Prove2me | Theorems.Thm_P2M_GlobalTheory_hdim__le_9c98933ce07b
-- name    : P2M_GlobalTheory_hdim__le_9c98933ce07b
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:11:59.912994+00:00
-- url     : https://prove2.me/theorems/cf315846-913c-55ba-b568-9fc3563a76e3
-- title:
--   P2 M Global Theory hdim  le 9c98933ce07b: P2 M Global Theory hdim  le 9c98933ce07b
-- statement:
--   The P2 M Global Theory hdim  le 9c98933ce07b construction uses the P2 M Global Theory hdim  le 9c98933ce07b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SumNegOnePowFinrankEqZero.lean#L313-L316
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SumNegOnePowFinrankEqZero.lean#L313-L316

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HdimEqZeroOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SumNegOnePowFinrankEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits Module
universe t v u
noncomputable section
open GlobalTheory
variable {X : Scheme.{u}}
variable (k : Type v) [Field k] [Algebra k Γ(X, ⊤)]
  {S : ShortComplex X.Modules} (hS : S.ShortExact)
include hS

theorem P2M_GlobalTheory_hdim__le_9c98933ce07b (n : ℕ) (h₂ : Module.Finite k (coh S.X₂ n))
    (h₁ : Module.Finite k (coh S.X₁ (n + 1))) :
    hdim k S.X₃ n ≤ hdim k S.X₂ n + hdim k S.X₁ (n + 1) := by sorry

alias «GlobalTheory».«hdim₃_le» := P2M_GlobalTheory_hdim__le_9c98933ce07b
