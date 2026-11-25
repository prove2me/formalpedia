-- Prove2me | Theorems.Thm_P2M_GlobalTheory_cohOn_forall_finite__9ed7f3adb97b
-- name    : P2M_GlobalTheory_cohOn_forall_finite__9ed7f3adb97b
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:11:41.925619+00:00
-- url     : https://prove2.me/theorems/bb252780-8e95-4847-a2b0-f4abef9d108d
-- title:
--   P2 M Global Theory coh On forall finite  9ed7f3adb97b: P2 M Global Theory coh On forall finite  9ed7f3adb97b
-- statement:
--   The P2 M Global Theory coh On forall finite  9ed7f3adb97b construction uses the P2 M Global Theory coh On forall finite  9ed7f3adb97b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SumNegOnePowFinrankEqZero.lean#L242-L244
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SumNegOnePowFinrankEqZero.lean#L242-L244

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

theorem P2M_GlobalTheory_cohOn_forall_finite__9ed7f3adb97b (h₁ : ∀ n, Module.Finite R (cohOn S.X₁ U n))
    (h₃ : ∀ n, Module.Finite R (cohOn S.X₃ U n)) : ∀ n, Module.Finite R (cohOn S.X₂ U n) := by sorry

alias «GlobalTheory».«cohOn».«forall_finite₂» := P2M_GlobalTheory_cohOn_forall_finite__9ed7f3adb97b
