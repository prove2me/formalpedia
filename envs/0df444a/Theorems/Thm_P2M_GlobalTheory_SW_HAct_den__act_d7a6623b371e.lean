-- Prove2me | Theorems.Thm_P2M_GlobalTheory_SW_HAct_den__act_d7a6623b371e
-- name    : P2M_GlobalTheory_SW_HAct_den__act_d7a6623b371e
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:44:31.871806+00:00
-- url     : https://prove2.me/theorems/1515d4d2-31f6-4609-9d19-9cb054f6fc67
-- title:
--   P2 M Global Theory SW HAct den  act d7a6623b371e: P2 M Global Theory SW HAct den  act d7a6623b371e
-- statement:
--   The P2 M Global Theory SW HAct den  act d7a6623b371e construction uses the P2 M Global Theory SW HAct den  act d7a6623b371e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/UnitaryActHalfSpace.lean#L62-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/UnitaryActHalfSpace.lean#L62-L67

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

theorem P2M_GlobalTheory_SW_HAct_den__act_d7a6623b371e (h1 : Aᴴ * C = Cᴴ * A) (h2 : Aᴴ * D = Cᴴ * B + 1) (h3 : Dᴴ * A = Bᴴ * C + 1)
    (h4 : Bᴴ * D = Dᴴ * B) (hQ : (C * Z + D).det ≠ 0) :
    (Z * Cᴴ + Dᴴ) * ((A * Z + B) * (C * Z + D)⁻¹) = Z * Aᴴ + Bᴴ := by sorry

alias «GlobalTheory».«SW».«HAct».«den'_act» := P2M_GlobalTheory_SW_HAct_den__act_d7a6623b371e
