-- Prove2me | Theorems.Thm_P2M_GlobalTheory_IsQuasiRegularSeq_of_isLocalizedModule__a22869f450cf
-- name    : P2M_GlobalTheory_IsQuasiRegularSeq_of_isLocalizedModule__a22869f450cf
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:05:50.885042+00:00
-- url     : https://prove2.me/theorems/44289940-1ce1-5712-bbd1-482079915fc3
-- title:
--   P2 M Global Theory Is Quasi Regular Seq of is Localized Module  a22869f450cf: P2 M Global Theory Is Quasi Regular Seq of is Localized Module  a22869f450cf
-- statement:
--   The P2 M Global Theory Is Quasi Regular Seq of is Localized Module  a22869f450cf construction uses the P2 M Global Theory Is Quasi Regular Seq of is Localized Module  a22869f450cf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasiRegularSeqSelfIffLocalizationMaximal.lean#L611-L615
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasiRegularSeqSelfIffLocalizationMaximal.lean#L611-L615

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsQuasiRegularSeqSelfIffLocalizationMaximal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
variable {R : Type*} [CommRing R] {ι : Type*} [Finite ι]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable (S : Type*) [CommRing S] [Algebra R S]
variable {N : Type*} [AddCommGroup N] [Module R N]

theorem P2M_GlobalTheory_IsQuasiRegularSeq_of_isLocalizedModule__a22869f450cf (T : Submonoid R) (g : M →ₗ[R] N)
    [IsLocalizedModule T g] {f : ι → R} (h : IsQuasiRegularSeq M f) : IsQuasiRegularSeq N f := by sorry

alias «GlobalTheory».«IsQuasiRegularSeq».«of_isLocalizedModule'» := P2M_GlobalTheory_IsQuasiRegularSeq_of_isLocalizedModule__a22869f450cf
