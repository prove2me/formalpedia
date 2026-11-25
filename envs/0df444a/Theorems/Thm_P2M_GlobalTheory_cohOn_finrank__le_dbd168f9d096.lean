-- Prove2me | Theorems.Thm_P2M_GlobalTheory_cohOn_finrank__le_dbd168f9d096
-- name    : P2M_GlobalTheory_cohOn_finrank__le_dbd168f9d096
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:12:16.880675+00:00
-- url     : https://prove2.me/theorems/367257d3-39db-4852-87d4-fe061d734c9c
-- title:
--   P2 M Global Theory coh On finrank  le dbd168f9d096: P2 M Global Theory coh On finrank  le dbd168f9d096
-- statement:
--   The P2 M Global Theory coh On finrank  le dbd168f9d096 construction uses the P2 M Global Theory coh On finrank  le dbd168f9d096 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SumNegOnePowFinrankEqZero.lean#L266-L270
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SumNegOnePowFinrankEqZero.lean#L266-L270

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

theorem P2M_GlobalTheory_cohOn_finrank__le_dbd168f9d096 (h₃ : Module.Finite k (cohOn S.X₃ U n))
    (h₂ : Module.Finite k (cohOn S.X₂ U (n + 1))) :
    finrank k (cohOn S.X₁ U (n + 1)) ≤
      finrank k (cohOn S.X₃ U n) + finrank k (cohOn S.X₂ U (n + 1)) := by sorry

alias «GlobalTheory».«cohOn».«finrank₁_le» := P2M_GlobalTheory_cohOn_finrank__le_dbd168f9d096
