-- Prove2me | Theorems.Thm_P2M_GlobalTheory_cohOn_subsingleton__f1f7d3cc4818
-- name    : P2M_GlobalTheory_cohOn_subsingleton__f1f7d3cc4818
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T21:42:35.517904+00:00
-- url     : https://prove2.me/theorems/d2e11f96-ff48-49a5-93aa-0bb6dee4d56a
-- title:
--   P2 M Global Theory coh On subsingleton  f1f7d3cc4818: P2 M Global Theory coh On subsingleton  f1f7d3cc4818
-- statement:
--   The P2 M Global Theory coh On subsingleton  f1f7d3cc4818 construction uses the P2 M Global Theory coh On subsingleton  f1f7d3cc4818 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SumNegOnePowFinrankEqZero.lean#L207-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SumNegOnePowFinrankEqZero.lean#L207-L209

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HdimEqZeroOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SumNegOnePowFinrankEqZero
import Theorems.Thm_P2M_GlobalTheory_SheafLES_subsingleton__c7111a18855b

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
include hS

theorem P2M_GlobalTheory_cohOn_subsingleton__f1f7d3cc4818 (h₂ : Subsingleton (cohOn S.X₂ U n))
    (h₁ : Subsingleton (cohOn S.X₁ U (n + 1))) : Subsingleton (cohOn S.X₃ U n) := by sorry

alias «GlobalTheory».«cohOn».«subsingleton₃» := P2M_GlobalTheory_cohOn_subsingleton__f1f7d3cc4818
