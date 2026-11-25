-- Prove2me | Theorems.Thm_P2M_GlobalTheory_PhiGam_ModPG_linearIndependent___5ce28352564c
-- name    : P2M_GlobalTheory_PhiGam_ModPG_linearIndependent___5ce28352564c
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:06:21.605856+00:00
-- url     : https://prove2.me/theorems/8b4f5b26-04ed-5a8e-80ee-938629a9cd26
-- title:
--   P2 M Global Theory Phi Gam Mod PG linear Independent   5ce28352564c: P2 M Global Theory Phi Gam Mod PG linear Independent   5ce28352564c
-- statement:
--   The P2 M Global Theory Phi Gam Mod PG linear Independent   5ce28352564c construction uses the P2 M Global Theory Phi Gam Mod PG linear Independent   5ce28352564c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/PowerSeriesOneAddConstMulXMulInv.lean#L180-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/PowerSeriesOneAddConstMulXMulInv.lean#L180-L185

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesOneAddConstMulXMulInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries
variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V]
variable [Module k V] {l n : ℕ} {R : RingPG k l}

theorem P2M_GlobalTheory_PhiGam_ModPG_linearIndependent___5ce28352564c (D : ModPG R n V) (i : ZMod n) {ι : Type} (b : Module.Basis ι k⸨X⸩ V) :
    LinearIndependent k⸨X⸩ fun j => D.φ i (b j) := by sorry

alias «GlobalTheory».«PhiGam».«ModPG».«linearIndependent_φ» := P2M_GlobalTheory_PhiGam_ModPG_linearIndependent___5ce28352564c
