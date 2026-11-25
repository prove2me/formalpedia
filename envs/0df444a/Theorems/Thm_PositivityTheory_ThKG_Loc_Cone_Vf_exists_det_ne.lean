-- Prove2me | Theorems.Thm_PositivityTheory_ThKG_Loc_Cone_Vf_exists_det_ne
-- name    : PositivityTheory.ThKG.Loc.Cone.Vf.exists_det_ne
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T14:00:30.512901+00:00
-- url     : https://prove2.me/theorems/a89adfdc-49ba-51f1-b264-50e53f2c7914
-- title:
--   Vf: exists det ne
-- statement:
--   The Vf construction uses the exists det ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ConeShifts/ExistsPowIdem.lean#L247-L303
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ConeShifts/ExistsPowIdem.lean#L247-L303

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

theorem PositivityTheory.ThKG.Loc.Cone.Vf.exists_det_ne {K : Type} [Field K] [Finite K] {k k' : Matrix β β K} (hk : k' * k = 1) {h δ : K} (hh : h + h = 1)
    (hδ : δ ≠ 0) : ∃ N, (1 + (1 - k) * ((-h) • 1 + δ • (1 - (1 + 1 + k + k') ^ N))).det ≠ 0 := by sorry
