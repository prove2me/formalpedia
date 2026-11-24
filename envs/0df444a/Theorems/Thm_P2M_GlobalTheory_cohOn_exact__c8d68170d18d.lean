-- Prove2me | Theorems.Thm_P2M_GlobalTheory_cohOn_exact__c8d68170d18d
-- name    : P2M_GlobalTheory_cohOn_exact__c8d68170d18d
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T21:42:58.529693+00:00
-- url     : https://prove2.me/theorems/f9e80be3-894e-448e-b1a8-400da51b90d0
-- title:
--   P2 M Global Theory coh On exact  c8d68170d18d: P2 M Global Theory coh On exact  c8d68170d18d
-- statement:
--   The P2 M Global Theory coh On exact  c8d68170d18d construction uses the P2 M Global Theory coh On exact  c8d68170d18d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SumNegOnePowFinrankEqZero.lean#L154-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SumNegOnePowFinrankEqZero.lean#L154-L155

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HdimEqZeroOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SumNegOnePowFinrankEqZero
import Theorems.Thm_P2M_GlobalTheory_SheafLES_exact__24269ba80ece

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

theorem P2M_GlobalTheory_cohOn_exact__c8d68170d18d : Function.Exact (map R S.g U n) (δ R hS U n) := by sorry

alias «GlobalTheory».«cohOn».«exact₃» := P2M_GlobalTheory_cohOn_exact__c8d68170d18d
