-- Prove2me | Theorems.Thm_P2M_GlobalTheory_cohOn___map_6ba3242e7e5e
-- name    : P2M_GlobalTheory_cohOn___map_6ba3242e7e5e
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T21:40:17.232819+00:00
-- url     : https://prove2.me/theorems/024152bb-b5b6-4601-9b3d-5e679cfda449
-- title:
--   P2 M Global Theory coh On   map 6ba3242e7e5e: P2 M Global Theory coh On   map 6ba3242e7e5e
-- statement:
--   The P2 M Global Theory coh On   map 6ba3242e7e5e construction uses the P2 M Global Theory coh On   map 6ba3242e7e5e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SumNegOnePowFinrankEqZero.lean#L169-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SumNegOnePowFinrankEqZero.lean#L169-L170

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HdimEqZeroOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SumNegOnePowFinrankEqZero
import Theorems.Thm_P2M_GlobalTheory_SheafLES___map_026ec4bafb10
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GlobalTheory_SheafLES___map_026ec4bafb10


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

theorem P2M_GlobalTheory_cohOn___map_6ba3242e7e5e (x : cohOn S.X₂ U n) : δ R hS U n (map R S.g U n x) = 0 := by sorry

alias «GlobalTheory».«cohOn».«δ_map» := P2M_GlobalTheory_cohOn___map_6ba3242e7e5e
