-- Prove2me | Theorems.Thm_P2M_GlobalTheory_hdim__le_b9cb39bd95c7
-- name    : P2M_GlobalTheory_hdim__le_b9cb39bd95c7
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:11:50.538227+00:00
-- url     : https://prove2.me/theorems/06045548-41d6-4711-97a0-26439daea3f2
-- title:
--   P2 M Global Theory hdim  le b9cb39bd95c7: P2 M Global Theory hdim  le b9cb39bd95c7
-- statement:
--   The P2 M Global Theory hdim  le b9cb39bd95c7 construction uses the P2 M Global Theory hdim  le b9cb39bd95c7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SumNegOnePowFinrankEqZero.lean#L309-L311
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SumNegOnePowFinrankEqZero.lean#L309-L311

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

theorem P2M_GlobalTheory_hdim__le_b9cb39bd95c7 (n : ℕ) (h₁ : Module.Finite k (coh S.X₁ n)) (h₃ : Module.Finite k (coh S.X₃ n)) :
    hdim k S.X₂ n ≤ hdim k S.X₁ n + hdim k S.X₃ n := by sorry

alias «GlobalTheory».«hdim₂_le» := P2M_GlobalTheory_hdim__le_b9cb39bd95c7
