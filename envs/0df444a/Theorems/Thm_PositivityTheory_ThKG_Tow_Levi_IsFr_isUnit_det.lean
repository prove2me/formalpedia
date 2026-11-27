-- Prove2me | Theorems.Thm_PositivityTheory_ThKG_Tow_Levi_IsFr_isUnit_det
-- name    : PositivityTheory.ThKG.Tow.Levi.IsFr.isUnit_det
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T14:01:30.855121+00:00
-- url     : https://prove2.me/theorems/cddd7650-739e-4b78-bcb7-5f12d1a3635c
-- title:
--   Is Fr: is Unit det
-- statement:
--   The Is Fr construction uses the is Unit det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/TowerModels/LeviAlg.lean#L43-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/TowerModels/LeviAlg.lean#L43-L53

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_TowerModels_LeviAlg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.Tow PositivityTheory.ThKG.Tow.Levi
open Matrix
variable {R S : Type} [CommRing R] [CommRing S] {d e : Type} [Fintype d] [DecidableEq d] [Fintype e] [DecidableEq e]
variable {c : R →+* R} {J : Matrix d d R} {J₁ : Matrix e e R} {ι : Matrix d e R} {x y : d → R}

theorem PositivityTheory.ThKG.Tow.Levi.IsFr.isUnit_det (h : IsFr c J J₁ ι x y) (hJ : IsUnit J.det) : IsUnit J₁.det := by sorry
