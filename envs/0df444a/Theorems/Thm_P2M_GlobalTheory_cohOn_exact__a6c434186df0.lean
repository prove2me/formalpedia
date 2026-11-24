-- Prove2me | Theorems.Thm_P2M_GlobalTheory_cohOn_exact__a6c434186df0
-- name    : P2M_GlobalTheory_cohOn_exact__a6c434186df0
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T21:42:19.099573+00:00
-- url     : https://prove2.me/theorems/1bb7b04b-0697-4882-9738-6650567318dd
-- title:
--   P2 M Global Theory coh On exact  a6c434186df0: P2 M Global Theory coh On exact  a6c434186df0
-- statement:
--   The P2 M Global Theory coh On exact  a6c434186df0 construction uses the P2 M Global Theory coh On exact  a6c434186df0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SumNegOnePowFinrankEqZero.lean#L157-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SumNegOnePowFinrankEqZero.lean#L157-L158

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HdimEqZeroOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SumNegOnePowFinrankEqZero
import Theorems.Thm_P2M_GlobalTheory_SheafLES_exact__5aa7b67be2da

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

theorem P2M_GlobalTheory_cohOn_exact__a6c434186df0 : Function.Exact (δ R hS U n) (map R S.f U (n + 1)) := by sorry

alias «GlobalTheory».«cohOn».«exact₁» := P2M_GlobalTheory_cohOn_exact__a6c434186df0
