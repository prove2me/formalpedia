-- Prove2me | Theorems.Thm_P2M_GlobalTheory_cohOn_finrank__le_2b3e184890cd
-- name    : P2M_GlobalTheory_cohOn_finrank__le_2b3e184890cd
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:11:56.081047+00:00
-- url     : https://prove2.me/theorems/c1a90590-c417-4180-8f23-853ebc50d3c0
-- title:
--   P2 M Global Theory coh On finrank  le 2b3e184890cd: P2 M Global Theory coh On finrank  le 2b3e184890cd
-- statement:
--   The P2 M Global Theory coh On finrank  le 2b3e184890cd construction uses the P2 M Global Theory coh On finrank  le 2b3e184890cd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SumNegOnePowFinrankEqZero.lean#L261-L264
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SumNegOnePowFinrankEqZero.lean#L261-L264

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
variable (k : Type v) [Field k] [Algebra k Γ(X, ⊤)]

theorem P2M_GlobalTheory_cohOn_finrank__le_2b3e184890cd (h₂ : Module.Finite k (cohOn S.X₂ U n))
    (h₁ : Module.Finite k (cohOn S.X₁ U (n + 1))) :
    finrank k (cohOn S.X₃ U n) ≤ finrank k (cohOn S.X₂ U n) + finrank k (cohOn S.X₁ U (n + 1)) := by sorry

alias «GlobalTheory».«cohOn».«finrank₃_le» := P2M_GlobalTheory_cohOn_finrank__le_2b3e184890cd
