-- Prove2me | Theorems.Thm_P2M_GlobalTheory_cohOn_finite__ff84c2925af6
-- name    : P2M_GlobalTheory_cohOn_finite__ff84c2925af6
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T21:42:09.820133+00:00
-- url     : https://prove2.me/theorems/1f58b53a-f2f1-4f3e-b57a-ad80308db237
-- title:
--   P2 M Global Theory coh On finite  ff84c2925af6: P2 M Global Theory coh On finite  ff84c2925af6
-- statement:
--   The P2 M Global Theory coh On finite  ff84c2925af6 construction uses the P2 M Global Theory coh On finite  ff84c2925af6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SumNegOnePowFinrankEqZero.lean#L230-L232
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SumNegOnePowFinrankEqZero.lean#L230-L232

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

theorem P2M_GlobalTheory_cohOn_finite__ff84c2925af6 (h₃ : Module.Finite R (cohOn S.X₃ U n))
    (h₂ : Module.Finite R (cohOn S.X₂ U (n + 1))) : Module.Finite R (cohOn S.X₁ U (n + 1)) := by sorry

alias «GlobalTheory».«cohOn».«finite₁» := P2M_GlobalTheory_cohOn_finite__ff84c2925af6
