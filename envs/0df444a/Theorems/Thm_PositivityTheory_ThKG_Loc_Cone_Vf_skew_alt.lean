-- Prove2me | Theorems.Thm_PositivityTheory_ThKG_Loc_Cone_Vf_skew_alt
-- name    : PositivityTheory.ThKG.Loc.Cone.Vf.skew_alt
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:05:20.007825+00:00
-- url     : https://prove2.me/theorems/ad74f733-15df-490d-a7a5-976da4c4e6a9
-- title:
--   Vf: skew alt
-- statement:
--   The Vf construction uses the skew alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ConeShifts/ExistsPowIdem.lean#L61-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ConeShifts/ExistsPowIdem.lean#L61-L102

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ConeShifts_ExistsPowIdem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.Loc PositivityTheory.ThKG.Loc.Cone PositivityTheory.ThKG.Loc.Cone.Vf
open Matrix GlobalTheory.WeilM
variable {R A β : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A) [Fintype β] [DecidableEq β]
variable {c} {J : Matrix β β A}

theorem PositivityTheory.ThKG.Loc.Cone.Vf.skew_alt {Ji k k' b b' f' : Matrix β β A} (hJ : J * Ji = 1) (hk : k * k' = 1) (a1 : Adj c J k k') (a2 : Adj c J k' k)
    (b1 : Adj c J b b') (b2 : Adj c J b' b) (hb : b + b' = -1) (hf : (1 + (1 - k) * b) * f' = 1) :
    (-(f' * (1 - k)))ᵀ * J + J * (-(f' * (1 - k))).map c = 0 := by sorry
