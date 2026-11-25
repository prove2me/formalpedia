-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_map_piece_65c72f83e5aa
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_map_piece_65c72f83e5aa
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:27:20.661815+00:00
-- url     : https://prove2.me/theorems/1e7b71ca-6882-4e4d-bf6e-d798eeeebf58
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Laurent Loc map piece 65c72f83e5aa: P2 M Ground Theory Heights  Heights Kleiman Laurent Loc map piece 65c72f83e5aa
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Laurent Loc map piece 65c72f83e5aa construction uses the P2 M Ground Theory Heights  Heights Kleiman Laurent Loc map piece 65c72f83e5aa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerrePolyLaurent.lean#L158-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerrePolyLaurent.lean#L158-L165

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsSerrePoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSerrePolyLaurent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.Kleiman.LaurentLoc
variable {S : Type u} [CommRing S] {N : ℕ}
attribute [local instance] algP

theorem P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_map_piece_65c72f83e5aa (c : ℤ) : ((polyGraded S N).piece c).map (polyToLaurent S N) =
    Finsupp.supported S S (laurentExps N c ∅) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«LaurentLoc».«map_piece» := P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_map_piece_65c72f83e5aa
