-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_mono_pullback_map_of_flat__68a0a7eac265
-- name    : P2M_GlobalTheory_T_mono_pullback_map_of_flat__68a0a7eac265
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:06:52.978802+00:00
-- url     : https://prove2.me/theorems/56dfef2b-0d5d-55de-98fd-fbd5d3eaf790
-- title:
--   P2 M Global Theory T mono pullback map of flat  68a0a7eac265: P2 M Global Theory T mono pullback map of flat  68a0a7eac265
-- statement:
--   The P2 M Global Theory T mono pullback map of flat  68a0a7eac265 construction uses the P2 M Global Theory T mono pullback map of flat  68a0a7eac265 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MonoPullbackMapOfFlatStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MonoPullbackMapOfFlatStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MonoPullbackMapOfFlat
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MonoPullbackMapOfFlatStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_mono_pullback_map_of_flat__68a0a7eac265 : ∀ (X Y : Scheme.{0}) (f : X ⟶ Y) [Flat f] (G G' : Y.Modules) (φ : G ⟶ G') [Mono φ], Mono ((Scheme.Modules.pullback f).map φ) := by sorry

alias «GlobalTheory».«T».«mono_pullback_map_of_flat'» := P2M_GlobalTheory_T_mono_pullback_map_of_flat__68a0a7eac265
