-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CMVal_Model_splits_of_mem__40e3e115741c
-- name    : P2M_GlobalTheory_CMVal_Model_splits_of_mem__40e3e115741c
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:02:45.709617+00:00
-- url     : https://prove2.me/theorems/e4d762ce-5b5a-43fe-b625-3f666f8ec7b9
-- title:
--   P2 M Global Theory CMVal Model splits of mem  40e3e115741c: P2 M Global Theory CMVal Model splits of mem  40e3e115741c
-- statement:
--   The P2 M Global Theory CMVal Model splits of mem  40e3e115741c construction uses the P2 M Global Theory CMVal Model splits of mem  40e3e115741c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExistsValuedHeckeCharRamified.lean#L399-L404
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExistsValuedHeckeCharRamified.lean#L399-L404

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

theorem P2M_GlobalTheory_CMVal_Model_splits_of_mem__40e3e115741c (v : HeightOneSpectrum (OF K)) (h : ((127 : ℕ) : OF K) ∈ v.asIdeal) : Splits v := by sorry

alias «GlobalTheory».«CMVal».«Model».«splits_of_mem'» := P2M_GlobalTheory_CMVal_Model_splits_of_mem__40e3e115741c
