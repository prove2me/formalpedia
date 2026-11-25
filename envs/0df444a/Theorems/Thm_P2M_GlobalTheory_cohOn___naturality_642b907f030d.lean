-- Prove2me | Theorems.Thm_P2M_GlobalTheory_cohOn___naturality_642b907f030d
-- name    : P2M_GlobalTheory_cohOn___naturality_642b907f030d
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:11:49.583499+00:00
-- url     : https://prove2.me/theorems/b4159d4f-412f-4e61-9af2-e3091ae28ff8
-- title:
--   P2 M Global Theory coh On   naturality 642b907f030d: P2 M Global Theory coh On   naturality 642b907f030d
-- statement:
--   The P2 M Global Theory coh On   naturality 642b907f030d construction uses the P2 M Global Theory coh On   naturality 642b907f030d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SumNegOnePowFinrankEqZero.lean#L175-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SumNegOnePowFinrankEqZero.lean#L175-L179

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HdimEqZeroOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SumNegOnePowFinrankEqZero
import Theorems.Thm_P2M_GlobalTheory_SheafLES___naturality_d0a1c18f99f7

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

theorem P2M_GlobalTheory_cohOn___naturality_642b907f030d {S' : ShortComplex X.Modules} (hS' : S'.ShortExact) (φ : S ⟶ S')
    (x : cohOn S.X₃ U n) :
    map R φ.τ₁ U (n + 1) (δ R hS U n x) = δ R hS' U n (map R φ.τ₃ U n x) := by sorry

alias «GlobalTheory».«cohOn».«δ_naturality» := P2M_GlobalTheory_cohOn___naturality_642b907f030d
