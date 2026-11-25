-- Prove2me | Theorems.Thm_P2M_GlobalTheory_cohOn_forall_finite__b9548819e78a
-- name    : P2M_GlobalTheory_cohOn_forall_finite__b9548819e78a
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:12:20.054407+00:00
-- url     : https://prove2.me/theorems/155d2255-4c01-4996-9699-77694943c359
-- title:
--   P2 M Global Theory coh On forall finite  b9548819e78a: P2 M Global Theory coh On forall finite  b9548819e78a
-- statement:
--   The P2 M Global Theory coh On forall finite  b9548819e78a construction uses the P2 M Global Theory coh On forall finite  b9548819e78a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SumNegOnePowFinrankEqZero.lean#L246-L248
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SumNegOnePowFinrankEqZero.lean#L246-L248

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

theorem P2M_GlobalTheory_cohOn_forall_finite__b9548819e78a (h₁ : ∀ n, Module.Finite R (cohOn S.X₁ U n))
    (h₂ : ∀ n, Module.Finite R (cohOn S.X₂ U n)) : ∀ n, Module.Finite R (cohOn S.X₃ U n) := by sorry

alias «GlobalTheory».«cohOn».«forall_finite₃» := P2M_GlobalTheory_cohOn_forall_finite__b9548819e78a
