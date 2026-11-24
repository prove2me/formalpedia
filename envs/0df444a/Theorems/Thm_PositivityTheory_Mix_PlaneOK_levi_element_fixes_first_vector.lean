-- Prove2me | Theorems.Thm_PositivityTheory_Mix_PlaneOK_levi_element_fixes_first_vector
-- name    : PositivityTheory.Mix.PlaneOK.levi_element_fixes_first_vector
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:46:09.868808+00:00
-- url     : https://prove2.me/theorems/e3378b8a-4ceb-4738-9da9-f2ae37da44ca
-- title:
--   Plane OK: levi element fixes first vector
-- statement:
--   The Plane OK construction uses the levi element fixes first vector property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/MixedModels/PlaneGen.lean#L102-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/MixedModels/PlaneGen.lean#L102-L106

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_MixedModels_PlaneGen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.Mix
open Matrix
variable {R : Type} [CommRing R] {n k : ℕ}
variable {c : R →+* R} {J : Matrix (Fin n) (Fin n) R}
open PositivityTheory.Mix.PlaneOK
variable {ε : R} {x y : Fin n → R} {ι : Matrix (Fin n) (Fin k) R} (h : PlaneOK c J ε x y ι)
include h

theorem PositivityTheory.Mix.PlaneOK.levi_element_fixes_first_vector (t s : R) : lev c J ε x y t s *ᵥ x = t • x := by sorry
