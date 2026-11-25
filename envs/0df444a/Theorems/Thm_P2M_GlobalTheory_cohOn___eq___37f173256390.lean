-- Prove2me | Theorems.Thm_P2M_GlobalTheory_cohOn___eq___37f173256390
-- name    : P2M_GlobalTheory_cohOn___eq___37f173256390
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:06:43.651828+00:00
-- url     : https://prove2.me/theorems/c283d9ef-f233-5141-a47a-bba7deaea4b3
-- title:
--   P2 M Global Theory coh On   eq   37f173256390: P2 M Global Theory coh On   eq   37f173256390
-- statement:
--   The P2 M Global Theory coh On   eq   37f173256390 construction uses the P2 M Global Theory coh On   eq   37f173256390 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SumNegOnePowFinrankEqZero.lean#L146-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SumNegOnePowFinrankEqZero.lean#L146-L147

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

theorem P2M_GlobalTheory_cohOn___eq___37f173256390 (R' : Type t) [CommRing R'] [Algebra R' Γ(X, ⊤)] (x : cohOn S.X₃ U n) :
    δ R hS U n x = δ R' hS U n x := by sorry

alias «GlobalTheory».«cohOn».«δ_eq_δ» := P2M_GlobalTheory_cohOn___eq___37f173256390
