-- Prove2me | Theorems.Thm_P2M_GlobalTheory_cohOn_subsingleton__0c81a4510352
-- name    : P2M_GlobalTheory_cohOn_subsingleton__0c81a4510352
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:12:07.203501+00:00
-- url     : https://prove2.me/theorems/0f7216b6-4d48-4afa-ba37-328bfc19c91f
-- title:
--   P2 M Global Theory coh On subsingleton  0c81a4510352: P2 M Global Theory coh On subsingleton  0c81a4510352
-- statement:
--   The P2 M Global Theory coh On subsingleton  0c81a4510352 construction uses the P2 M Global Theory coh On subsingleton  0c81a4510352 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SumNegOnePowFinrankEqZero.lean#L211-L213
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SumNegOnePowFinrankEqZero.lean#L211-L213

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HdimEqZeroOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SumNegOnePowFinrankEqZero
import Theorems.Thm_P2M_GlobalTheory_SheafLES_subsingleton__430f6995ae54

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

theorem P2M_GlobalTheory_cohOn_subsingleton__0c81a4510352 (h₃ : Subsingleton (cohOn S.X₃ U n))
    (h₂ : Subsingleton (cohOn S.X₂ U (n + 1))) : Subsingleton (cohOn S.X₁ U (n + 1)) := by sorry

alias «GlobalTheory».«cohOn».«subsingleton₁» := P2M_GlobalTheory_cohOn_subsingleton__0c81a4510352
