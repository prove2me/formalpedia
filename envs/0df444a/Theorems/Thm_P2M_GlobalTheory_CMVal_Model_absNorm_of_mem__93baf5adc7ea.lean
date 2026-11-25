-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CMVal_Model_absNorm_of_mem__93baf5adc7ea
-- name    : P2M_GlobalTheory_CMVal_Model_absNorm_of_mem__93baf5adc7ea
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:02:45.460611+00:00
-- url     : https://prove2.me/theorems/cfc0a6ab-0666-4559-8456-79de2861a283
-- title:
--   P2 M Global Theory CMVal Model abs Norm of mem  93baf5adc7ea: P2 M Global Theory CMVal Model abs Norm of mem  93baf5adc7ea
-- statement:
--   The P2 M Global Theory CMVal Model abs Norm of mem  93baf5adc7ea construction uses the P2 M Global Theory CMVal Model abs Norm of mem  93baf5adc7ea property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExistsValuedHeckeCharRamified.lean#L384-L397
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExistsValuedHeckeCharRamified.lean#L384-L397

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOfVal
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnramBridgeHolds
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExistsValuedHeckeCharRamified
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.Model

theorem P2M_GlobalTheory_CMVal_Model_absNorm_of_mem__93baf5adc7ea (P : HeightOneSpectrum (𝓞 K)) (h : ((127 : ℕ) : 𝓞 K) ∈ P.asIdeal) : Ideal.absNorm P.asIdeal = 127 := by sorry

alias «GlobalTheory».«CMVal».«Model».«absNorm_of_mem'» := P2M_GlobalTheory_CMVal_Model_absNorm_of_mem__93baf5adc7ea
