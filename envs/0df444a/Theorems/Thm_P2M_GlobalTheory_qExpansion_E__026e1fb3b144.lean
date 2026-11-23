-- Prove2me | Theorems.Thm_P2M_GlobalTheory_qExpansion_E__026e1fb3b144
-- name    : P2M_GlobalTheory_qExpansion_E__026e1fb3b144
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:22:03.06263+00:00
-- url     : https://prove2.me/theorems/c08ff6f3-dbdc-4059-a6ca-5c0f0292ff56
-- title:
--   P2 M Global Theory q Expansion E  026e1fb3b144: P2 M Global Theory q Expansion E  026e1fb3b144
-- statement:
--   The P2 M Global Theory q Expansion E  026e1fb3b144 construction uses the P2 M Global Theory q Expansion E  026e1fb3b144 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsPolynomialModularJOfHasQExpansion.lean#L62-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsPolynomialModularJOfHasQExpansion.lean#L62-L69

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasQExpansionModularForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsPolynomialModularJOfHasQExpansion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperHalfPlane ModularForm Complex Function Filter PowerSeries
open scoped Topology MatrixGroups Manifold Real ArithmeticFunction.sigma
noncomputable section
open GlobalTheory
local notation "𝕢" => Function.Periodic.qParam

theorem P2M_GlobalTheory_qExpansion_E__026e1fb3b144 : qExpansion 1 E₄ =
    PowerSeries.map (Int.castRingHom ℂ) (1 + 240 * PowerSeries.mk fun n ↦ (σ 3 n : ℤ)) := by sorry

alias «GlobalTheory».«qExpansion_E₄» := P2M_GlobalTheory_qExpansion_E__026e1fb3b144
