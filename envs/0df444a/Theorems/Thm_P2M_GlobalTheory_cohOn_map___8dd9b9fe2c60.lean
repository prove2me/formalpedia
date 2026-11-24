-- Prove2me | Theorems.Thm_P2M_GlobalTheory_cohOn_map___8dd9b9fe2c60
-- name    : P2M_GlobalTheory_cohOn_map___8dd9b9fe2c60
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T21:42:43.804804+00:00
-- url     : https://prove2.me/theorems/11b74671-084c-4b65-a36c-51b7b4ce0898
-- title:
--   P2 M Global Theory coh On map   8dd9b9fe2c60: P2 M Global Theory coh On map   8dd9b9fe2c60
-- statement:
--   The P2 M Global Theory coh On map   8dd9b9fe2c60 construction uses the P2 M Global Theory coh On map   8dd9b9fe2c60 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SumNegOnePowFinrankEqZero.lean#L172-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SumNegOnePowFinrankEqZero.lean#L172-L173

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HdimEqZeroOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SumNegOnePowFinrankEqZero
import Theorems.Thm_P2M_GlobalTheory_SheafLES_map___ee3a67e9aebf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GlobalTheory_SheafLES_map___ee3a67e9aebf


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

theorem P2M_GlobalTheory_cohOn_map___8dd9b9fe2c60 (x : cohOn S.X₃ U n) : map R S.f U (n + 1) (δ R hS U n x) = 0 := by sorry

alias «GlobalTheory».«cohOn».«map_δ» := P2M_GlobalTheory_cohOn_map___8dd9b9fe2c60
