-- Prove2me | Theorems.Thm_P2M_GlobalTheory_hdim__le_f17fed8a4980
-- name    : P2M_GlobalTheory_hdim__le_f17fed8a4980
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:13:32.773076+00:00
-- url     : https://prove2.me/theorems/5971c2fc-1938-4f11-8bdf-e3d368a25cb6
-- title:
--   P2 M Global Theory hdim  le f17fed8a4980: P2 M Global Theory hdim  le f17fed8a4980
-- statement:
--   The P2 M Global Theory hdim  le f17fed8a4980 construction uses the P2 M Global Theory hdim  le f17fed8a4980 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SumNegOnePowFinrankEqZero.lean#L318-L321
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SumNegOnePowFinrankEqZero.lean#L318-L321

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

theorem P2M_GlobalTheory_hdim__le_f17fed8a4980 (n : ℕ) (h₃ : Module.Finite k (coh S.X₃ n))
    (h₂ : Module.Finite k (coh S.X₂ (n + 1))) :
    hdim k S.X₁ (n + 1) ≤ hdim k S.X₃ n + hdim k S.X₂ (n + 1) := by sorry

alias «GlobalTheory».«hdim₁_le» := P2M_GlobalTheory_hdim__le_f17fed8a4980
