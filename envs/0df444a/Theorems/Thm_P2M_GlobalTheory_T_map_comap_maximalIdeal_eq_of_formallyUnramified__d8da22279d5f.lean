-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_map_comap_maximalIdeal_eq_of_formallyUnramified__d8da22279d5f
-- name    : P2M_GlobalTheory_T_map_comap_maximalIdeal_eq_of_formallyUnramified__d8da22279d5f
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:06:35.818282+00:00
-- url     : https://prove2.me/theorems/a3c03851-bc3d-4d51-a947-33657b62845c
-- title:
--   P2 M Global Theory T map comap maximal Ideal eq of formally Unramified  d8da22279d5f: P2 M Global Theory T map comap maximal Ideal eq of formally Unramified  d8da22279d5f
-- statement:
--   The P2 M Global Theory T map comap maximal Ideal eq of formally Unramified  d8da22279d5f construction uses the P2 M Global Theory T map comap maximal Ideal eq of formally Unramified  d8da22279d5f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MapComapMaximalIdealEqOfFormallyUnramifiedStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MapComapMaximalIdealEqOfFormallyUnramifiedStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MapComapMaximalIdealEqOfFormallyUnramified
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MapComapMaximalIdealEqOfFormallyUnramifiedStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_map_comap_maximalIdeal_eq_of_formallyUnramified__d8da22279d5f : ∀ (A B : Type) [CommRing A] [CommRing B] [IsLocalRing B] [Algebra A B] [Algebra.FormallyUnramified A B] [Algebra.EssFiniteType A B], ((IsLocalRing.maximalIdeal B).comap (algebraMap A B)).map (algebraMap A B) = IsLocalRing.maximalIdeal B := by sorry

alias «GlobalTheory».«T».«map_comap_maximalIdeal_eq_of_formallyUnramified'» := P2M_GlobalTheory_T_map_comap_maximalIdeal_eq_of_formallyUnramified__d8da22279d5f
