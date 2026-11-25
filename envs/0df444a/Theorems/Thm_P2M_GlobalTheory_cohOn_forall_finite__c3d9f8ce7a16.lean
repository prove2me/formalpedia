-- Prove2me | Theorems.Thm_P2M_GlobalTheory_cohOn_forall_finite__c3d9f8ce7a16
-- name    : P2M_GlobalTheory_cohOn_forall_finite__c3d9f8ce7a16
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:12:04.577495+00:00
-- url     : https://prove2.me/theorems/041c7ded-c448-4995-b9e0-eeab6a8fbde0
-- title:
--   P2 M Global Theory coh On forall finite  c3d9f8ce7a16: P2 M Global Theory coh On forall finite  c3d9f8ce7a16
-- statement:
--   The P2 M Global Theory coh On forall finite  c3d9f8ce7a16 construction uses the P2 M Global Theory coh On forall finite  c3d9f8ce7a16 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SumNegOnePowFinrankEqZero.lean#L237-L240
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SumNegOnePowFinrankEqZero.lean#L237-L240

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
include hS
variable [IsNoetherianRing R]

theorem P2M_GlobalTheory_cohOn_forall_finite__c3d9f8ce7a16 (h₂ : ∀ n, Module.Finite R (cohOn S.X₂ U n))
    (h₃ : ∀ n, Module.Finite R (cohOn S.X₃ U n)) : ∀ n, Module.Finite R (cohOn S.X₁ U n)
  := by sorry

alias «GlobalTheory».«cohOn».«forall_finite₁» := P2M_GlobalTheory_cohOn_forall_finite__c3d9f8ce7a16
