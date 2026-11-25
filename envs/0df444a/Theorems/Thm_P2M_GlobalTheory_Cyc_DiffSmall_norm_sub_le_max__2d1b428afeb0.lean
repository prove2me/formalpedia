-- Prove2me | Theorems.Thm_P2M_GlobalTheory_Cyc_DiffSmall_norm_sub_le_max__2d1b428afeb0
-- name    : P2M_GlobalTheory_Cyc_DiffSmall_norm_sub_le_max__2d1b428afeb0
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T14:03:35.052619+00:00
-- url     : https://prove2.me/theorems/806dd0e4-ef1d-5cc2-a7ab-ca667f076294
-- title:
--   P2 M Global Theory Cyc Diff Small norm sub le max  2d1b428afeb0: P2 M Global Theory Cyc Diff Small norm sub le max  2d1b428afeb0
-- statement:
--   The P2 M Global Theory Cyc Diff Small norm sub le max  2d1b428afeb0 construction uses the P2 M Global Theory Cyc Diff Small norm sub le max  2d1b428afeb0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsTraceNormGe.lean#L25-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsTraceNormGe.lean#L25-L27

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AvMono
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsCycCycChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicCharacterPadicBasicProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FinrankCyclotomicExtAndCyclotomicCharSurjectiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegersEqSumZetaPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsTraceNormGe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc Polynomial
noncomputable section
open GlobalTheory GlobalTheory.Cyc
open GlobalTheory.Cyc.DiffSmall
variable {l : ℕ} [Fact l.Prime]

theorem P2M_GlobalTheory_Cyc_DiffSmall_norm_sub_le_max__2d1b428afeb0 (a b : Om l) : ‖a - b‖ ≤ max ‖a‖ ‖b‖ := by sorry

alias «GlobalTheory».«Cyc».«DiffSmall».«norm_sub_le_max'» := P2M_GlobalTheory_Cyc_DiffSmall_norm_sub_le_max__2d1b428afeb0
