-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_eq_map_maximalIdeal_of_ringKrullDim_eq_one__f360875eaa41
-- name    : P2M_GlobalTheory_T_eq_map_maximalIdeal_of_ringKrullDim_eq_one__f360875eaa41
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:06:29.736389+00:00
-- url     : https://prove2.me/theorems/b6cc31ff-e710-4eb9-9625-1b2b162a5ec1
-- title:
--   P2 M Global Theory T eq map maximal Ideal of ring Krull Dim eq one  f360875eaa41: P2 M Global Theory T eq map maximal Ideal of ring Krull Dim eq one  f360875eaa41
-- statement:
--   The P2 M Global Theory T eq map maximal Ideal of ring Krull Dim eq one  f360875eaa41 construction uses the P2 M Global Theory T eq map maximal Ideal of ring Krull Dim eq one  f360875eaa41 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EqMapMaximalIdealOfRingKrullDimEqOneStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EqMapMaximalIdealOfRingKrullDimEqOneStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EqMapMaximalIdealOfRingKrullDimEqOne
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EqMapMaximalIdealOfRingKrullDimEqOneStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_eq_map_maximalIdeal_of_ringKrullDim_eq_one__f360875eaa41 : ∀ (R A : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing A] [IsDomain A] [Algebra R A] [Module.Flat R A] (p : Ideal A) [p.IsPrime], (maximalIdeal R).map (algebraMap R A) ≤ p → ringKrullDim (Localization.AtPrime p) = 1 → IsDomain (A ⧸ (maximalIdeal R).map (algebraMap R A)) → p = (maximalIdeal R).map (algebraMap R A) := by sorry

alias «GlobalTheory».«T».«eq_map_maximalIdeal_of_ringKrullDim_eq_one'» := P2M_GlobalTheory_T_eq_map_maximalIdeal_of_ringKrullDim_eq_one__f360875eaa41
