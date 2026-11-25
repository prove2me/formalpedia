-- Prove2me | Theorems.Thm_PositivityTheory_Mix_PlaneOK_exists_lev
-- name    : PositivityTheory.Mix.PlaneOK.exists_lev
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:51:14.539951+00:00
-- url     : https://prove2.me/theorems/2b548f96-923d-402e-b4f7-a3b42692bf37
-- title:
--   Plane OK: exists lev
-- statement:
--   The Plane OK construction uses the exists lev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/MixedModels/PlaneGen.lean#L143-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/MixedModels/PlaneGen.lean#L143-L150

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

theorem PositivityTheory.Mix.PlaneOK.exists_lev (t : Rˣ) : ∃ m : GL (Fin n) R, m.1ᵀ * J * m.1.map c = J ∧ m.1 *ᵥ x = t.1 • x ∧ m.1 *ᵥ y = c (t⁻¹).1 • y ∧
    ∀ z, m.1 *ᵥ (ι *ᵥ z) = ι *ᵥ z := by sorry
