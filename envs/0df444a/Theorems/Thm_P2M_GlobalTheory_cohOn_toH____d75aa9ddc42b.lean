-- Prove2me | Theorems.Thm_P2M_GlobalTheory_cohOn_toH____d75aa9ddc42b
-- name    : P2M_GlobalTheory_cohOn_toH____d75aa9ddc42b
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T21:41:40.790372+00:00
-- url     : https://prove2.me/theorems/efd46c65-1947-4945-b998-277a2e99b89d
-- title:
--   P2 M Global Theory coh On to H    d75aa9ddc42b: P2 M Global Theory coh On to H    d75aa9ddc42b
-- statement:
--   The P2 M Global Theory coh On to H    d75aa9ddc42b construction uses the P2 M Global Theory coh On to H    d75aa9ddc42b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SumNegOnePowFinrankEqZero.lean#L142-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SumNegOnePowFinrankEqZero.lean#L142-L144

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
open GlobalTheory.cohOn
variable (R : Type v) [CommRing R] [Algebra R Γ(X, ⊤)]
  {S : ShortComplex X.Modules} (hS : S.ShortExact)
variable (U : X.Opens) (n : ℕ)

theorem P2M_GlobalTheory_cohOn_toH____d75aa9ddc42b (x : cohOn S.X₃ U n) :
    toH' S.X₁ U (n + 1) (δ R hS U n x) =
      SheafLES.δ.{u} (shortExact_toAbSheaf hS) n U (toH' S.X₃ U n x) := by sorry

alias «GlobalTheory».«cohOn».«toH'_δ» := P2M_GlobalTheory_cohOn_toH____d75aa9ddc42b
