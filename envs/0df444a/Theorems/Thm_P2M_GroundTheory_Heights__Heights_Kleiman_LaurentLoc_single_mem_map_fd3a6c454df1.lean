-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_single_mem_map_fd3a6c454df1
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_single_mem_map_fd3a6c454df1
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:27:23.805633+00:00
-- url     : https://prove2.me/theorems/77b3ae2b-11b9-4047-a777-7ebf0655a6d7
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Laurent Loc single mem map fd3a6c454df1: P2 M Ground Theory Heights  Heights Kleiman Laurent Loc single mem map fd3a6c454df1
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Laurent Loc single mem map fd3a6c454df1 construction uses the P2 M Ground Theory Heights  Heights Kleiman Laurent Loc single mem map fd3a6c454df1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerrePolyLaurent.lean#L234-L262
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerrePolyLaurent.lean#L234-L262

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_single_mem_map_fd3a6c454df1 (c : ℤ) (I : StdCell N) (x : Fin (N + 1) → ℤ) (hx : x ∈ laurentExps N c I.1) :
    Finsupp.single x (1 : S) ∈ (degLoc (polyGraded S N) c I).map (iota I) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«LaurentLoc».«single_mem_map» := P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_single_mem_map_fd3a6c454df1
