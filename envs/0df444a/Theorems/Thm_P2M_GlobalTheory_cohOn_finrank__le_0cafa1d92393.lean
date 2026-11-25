-- Prove2me | Theorems.Thm_P2M_GlobalTheory_cohOn_finrank__le_0cafa1d92393
-- name    : P2M_GlobalTheory_cohOn_finrank__le_0cafa1d92393
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:11:50.882538+00:00
-- url     : https://prove2.me/theorems/1592a27a-992d-4b2d-9705-2f9ef0b492e3
-- title:
--   P2 M Global Theory coh On finrank  le 0cafa1d92393: P2 M Global Theory coh On finrank  le 0cafa1d92393
-- statement:
--   The P2 M Global Theory coh On finrank  le 0cafa1d92393 construction uses the P2 M Global Theory coh On finrank  le 0cafa1d92393 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SumNegOnePowFinrankEqZero.lean#L256-L259
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SumNegOnePowFinrankEqZero.lean#L256-L259

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

theorem P2M_GlobalTheory_cohOn_finrank__le_0cafa1d92393 (h₁ : Module.Finite k (cohOn S.X₁ U n))
    (h₃ : Module.Finite k (cohOn S.X₃ U n)) :
    finrank k (cohOn S.X₂ U n) ≤ finrank k (cohOn S.X₁ U n) + finrank k (cohOn S.X₃ U n) := by sorry

alias «GlobalTheory».«cohOn».«finrank₂_le» := P2M_GlobalTheory_cohOn_finrank__le_0cafa1d92393
