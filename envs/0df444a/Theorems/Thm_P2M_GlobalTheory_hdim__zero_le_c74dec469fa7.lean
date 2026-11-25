-- Prove2me | Theorems.Thm_P2M_GlobalTheory_hdim__zero_le_c74dec469fa7
-- name    : P2M_GlobalTheory_hdim__zero_le_c74dec469fa7
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:07:17.033057+00:00
-- url     : https://prove2.me/theorems/9d5e12c4-f971-48c3-ac5c-74e82e3b70d3
-- title:
--   P2 M Global Theory hdim  zero le c74dec469fa7: P2 M Global Theory hdim  zero le c74dec469fa7
-- statement:
--   The P2 M Global Theory hdim  zero le c74dec469fa7 construction uses the P2 M Global Theory hdim  zero le c74dec469fa7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SumNegOnePowFinrankEqZero.lean#L323-L324
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SumNegOnePowFinrankEqZero.lean#L323-L324

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

theorem P2M_GlobalTheory_hdim__zero_le_c74dec469fa7 (h₂ : Module.Finite k (coh S.X₂ 0)) : hdim k S.X₁ 0 ≤ hdim k S.X₂ 0 := by sorry

alias «GlobalTheory».«hdim₁_zero_le» := P2M_GlobalTheory_hdim__zero_le_c74dec469fa7
