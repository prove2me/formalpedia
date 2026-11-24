-- Prove2me | Theorems.Thm_PositivityTheory_ThKG_Loc_Cone_Vf_Adj_mul
-- name    : PositivityTheory.ThKG.Loc.Cone.Vf.Adj.mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:57:04.22113+00:00
-- url     : https://prove2.me/theorems/139d1a28-db28-4b56-bb85-6ef56df9b58b
-- title:
--   Adj: mul
-- statement:
--   The Adj construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ConeShifts/ExistsPowIdem.lean#L41-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ConeShifts/ExistsPowIdem.lean#L41-L43

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

theorem PositivityTheory.ThKG.Loc.Cone.Vf.Adj.mul {M M' N N' : Matrix β β A} (h : Adj c J M M') (h' : Adj c J N N') : Adj c J (M * N) (N' * M') := by sorry
