-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CMVal_Model_exists_place__00af12d7f4b9
-- name    : P2M_GlobalTheory_CMVal_Model_exists_place__00af12d7f4b9
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:03:00.43817+00:00
-- url     : https://prove2.me/theorems/57c41ae3-4a68-42e5-afd4-d9abe097086f
-- title:
--   P2 M Global Theory CMVal Model exists place  00af12d7f4b9: P2 M Global Theory CMVal Model exists place  00af12d7f4b9
-- statement:
--   The P2 M Global Theory CMVal Model exists place  00af12d7f4b9 construction uses the P2 M Global Theory CMVal Model exists place  00af12d7f4b9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExistsValuedHeckeCharRamified.lean#L406-L412
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExistsValuedHeckeCharRamified.lean#L406-L412

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

theorem P2M_GlobalTheory_CMVal_Model_exists_place__00af12d7f4b9 : ∃ v : HeightOneSpectrum (OF K), ((127 : ℕ) : OF K) ∈ v.asIdeal := by sorry

alias «GlobalTheory».«CMVal».«Model».«exists_place'» := P2M_GlobalTheory_CMVal_Model_exists_place__00af12d7f4b9
