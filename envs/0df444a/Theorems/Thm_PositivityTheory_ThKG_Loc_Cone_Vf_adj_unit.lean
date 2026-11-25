-- Prove2me | Theorems.Thm_PositivityTheory_ThKG_Loc_Cone_Vf_adj_unit
-- name    : PositivityTheory.ThKG.Loc.Cone.Vf.adj_unit
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T09:05:31.77473+00:00
-- url     : https://prove2.me/theorems/1848acab-7728-5e26-bb26-2e1e8549d4c1
-- title:
--   Vf: adj unit
-- statement:
--   The Vf construction uses the adj unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ConeShifts/ExistsPowIdem.lean#L53-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ConeShifts/ExistsPowIdem.lean#L53-L59

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

theorem PositivityTheory.ThKG.Loc.Cone.Vf.adj_unit (k : UG c J) : Adj c J (k.1 : Matrix β β A) (k⁻¹).1 := by sorry
