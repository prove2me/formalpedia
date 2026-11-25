-- Prove2me | Theorems.Thm_P2M_Formalism_CoboundaryTransfers_WachMod_mem_cocycles__3712a15bf5f6
-- name    : P2M_Formalism_CoboundaryTransfers_WachMod_mem_cocycles__3712a15bf5f6
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:53:13.84893+00:00
-- url     : https://prove2.me/theorems/de2efbc7-ddab-40c4-b0bd-1135ce3eed6f
-- title:
--   P2 M Formalism Coboundary Transfers Wach Mod mem cocycles  3712a15bf5f6: P2 M Formalism Coboundary Transfers Wach Mod mem cocycles  3712a15bf5f6
-- statement:
--   The P2 M Formalism Coboundary Transfers Wach Mod mem cocycles  3712a15bf5f6 construction uses the P2 M Formalism Coboundary Transfers Wach Mod mem cocycles  3712a15bf5f6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CoboundaryTransfers/GammaStableTransfers/MemCoboundariesOfIsOneCoboundary.lean#L177-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CoboundaryTransfers/GammaStableTransfers/MemCoboundariesOfIsOneCoboundary.lean#L177-L177

import Definitions.Def_Formalism_CoboundaryTransfers_StatementAPI
import Definitions.Def_Formalism_CoboundaryTransfers_GammaStableTransfers_MemCoboundariesOfIsOneCoboundary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.CoboundaryTransfers
open Formalism.CoboundaryTransfers.WachMod
variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {B : Base O A} {M : ℕ}
  {D : Type} [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]
  (W : WachMod B M D)

theorem P2M_Formalism_CoboundaryTransfers_WachMod_mem_cocycles__3712a15bf5f6 (pr : D × D) : pr ∈ W.Z1 ↔ W.d1 pr.1 pr.2 = 0 := by sorry

alias «Formalism».«CoboundaryTransfers».«WachMod».«mem_cocycles'» := P2M_Formalism_CoboundaryTransfers_WachMod_mem_cocycles__3712a15bf5f6
