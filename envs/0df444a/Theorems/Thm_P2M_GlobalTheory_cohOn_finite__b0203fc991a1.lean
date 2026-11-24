-- Prove2me | Theorems.Thm_P2M_GlobalTheory_cohOn_finite__b0203fc991a1
-- name    : P2M_GlobalTheory_cohOn_finite__b0203fc991a1
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:40:32.804003+00:00
-- url     : https://prove2.me/theorems/ec6cb6b6-8c1a-4793-a720-0a802ed1bd8a
-- title:
--   P2 M Global Theory coh On finite  b0203fc991a1: P2 M Global Theory coh On finite  b0203fc991a1
-- statement:
--   The P2 M Global Theory coh On finite  b0203fc991a1 construction uses the P2 M Global Theory coh On finite  b0203fc991a1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SumNegOnePowFinrankEqZero.lean#L226-L228
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SumNegOnePowFinrankEqZero.lean#L226-L228

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

theorem P2M_GlobalTheory_cohOn_finite__b0203fc991a1 (h₂ : Module.Finite R (cohOn S.X₂ U n))
    (h₁ : Module.Finite R (cohOn S.X₁ U (n + 1))) : Module.Finite R (cohOn S.X₃ U n) := by sorry

alias «GlobalTheory».«cohOn».«finite₃» := P2M_GlobalTheory_cohOn_finite__b0203fc991a1
