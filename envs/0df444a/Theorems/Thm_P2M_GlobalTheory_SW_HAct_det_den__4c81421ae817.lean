-- Prove2me | Theorems.Thm_P2M_GlobalTheory_SW_HAct_det_den__4c81421ae817
-- name    : P2M_GlobalTheory_SW_HAct_det_den__4c81421ae817
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:08:47.836516+00:00
-- url     : https://prove2.me/theorems/cfe895f5-1547-4ec3-8b04-2758593f827c
-- title:
--   P2 M Global Theory SW HAct det den  4c81421ae817: P2 M Global Theory SW HAct det den  4c81421ae817
-- statement:
--   The P2 M Global Theory SW HAct det den  4c81421ae817 construction uses the P2 M Global Theory SW HAct det den  4c81421ae817 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/UnitaryActHalfSpace.lean#L69-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/UnitaryActHalfSpace.lean#L69-L89

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HAct
variable {N : ℕ} {A B C D Z : Matrix (Fin N) (Fin N) ℂ}

theorem P2M_GlobalTheory_SW_HAct_det_den__4c81421ae817 (h1 : Aᴴ * C = Cᴴ * A) (h2 : Aᴴ * D = Cᴴ * B + 1) (h3 : Dᴴ * A = Bᴴ * C + 1)
    (h4 : Bᴴ * D = Dᴴ * B) (hQ : (C * Z + D).det ≠ 0) :
    (Z * Cᴴ + Dᴴ).det * (fromBlocks A B C D).det = (C * Z + D).det := by sorry

alias «GlobalTheory».«SW».«HAct».«det_den'» := P2M_GlobalTheory_SW_HAct_det_den__4c81421ae817
