-- Prove2me | Theorems.Thm_P2M_GlobalTheory_PhiGam_ModPG_span___b6f5a61103e8
-- name    : P2M_GlobalTheory_PhiGam_ModPG_span___b6f5a61103e8
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:08:05.639364+00:00
-- url     : https://prove2.me/theorems/ac453b03-adf0-47aa-bfa8-29b7636f0b66
-- title:
--   P2 M Global Theory Phi Gam Mod PG span   b6f5a61103e8: P2 M Global Theory Phi Gam Mod PG span   b6f5a61103e8
-- statement:
--   The P2 M Global Theory Phi Gam Mod PG span   b6f5a61103e8 construction uses the P2 M Global Theory Phi Gam Mod PG span   b6f5a61103e8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/PowerSeriesOneAddConstMulXMulInv.lean#L168-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/PowerSeriesOneAddConstMulXMulInv.lean#L168-L178

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

theorem P2M_GlobalTheory_PhiGam_ModPG_span___b6f5a61103e8 (D : ModPG R n V) (i : ZMod n) {ι : Type} (b : Module.Basis ι k⸨X⸩ V) :
    Submodule.span k⸨X⸩ (Set.range fun j => D.φ i (b j)) = ⊤ := by sorry

alias «GlobalTheory».«PhiGam».«ModPG».«span_φ» := P2M_GlobalTheory_PhiGam_ModPG_span___b6f5a61103e8
