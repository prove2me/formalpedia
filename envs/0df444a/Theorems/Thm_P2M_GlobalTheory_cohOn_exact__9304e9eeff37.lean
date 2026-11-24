-- Prove2me | Theorems.Thm_P2M_GlobalTheory_cohOn_exact__9304e9eeff37
-- name    : P2M_GlobalTheory_cohOn_exact__9304e9eeff37
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T21:40:42.620798+00:00
-- url     : https://prove2.me/theorems/a9ebf679-fbdb-4248-916b-3dff7f051906
-- title:
--   P2 M Global Theory coh On exact  9304e9eeff37: P2 M Global Theory coh On exact  9304e9eeff37
-- statement:
--   The P2 M Global Theory coh On exact  9304e9eeff37 construction uses the P2 M Global Theory coh On exact  9304e9eeff37 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SumNegOnePowFinrankEqZero.lean#L151-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SumNegOnePowFinrankEqZero.lean#L151-L152

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HdimEqZeroOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SumNegOnePowFinrankEqZero
import Theorems.Thm_P2M_GlobalTheory_SheafLES_exact__a6249fcd4aae

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

theorem P2M_GlobalTheory_cohOn_exact__9304e9eeff37 : Function.Exact (map R S.f U n) (map R S.g U n) := by sorry

alias «GlobalTheory».«cohOn».«exact₂» := P2M_GlobalTheory_cohOn_exact__9304e9eeff37
