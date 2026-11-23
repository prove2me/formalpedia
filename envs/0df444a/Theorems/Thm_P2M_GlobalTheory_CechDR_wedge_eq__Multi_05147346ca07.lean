-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CechDR_wedge_eq__Multi_05147346ca07
-- name    : P2M_GlobalTheory_CechDR_wedge_eq__Multi_05147346ca07
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:36:07.031911+00:00
-- url     : https://prove2.me/theorems/ba43e5a2-54df-4bfb-b99b-f94e48f9f38b
-- title:
--   P2 M Global Theory Cech DR wedge eq  Multi 05147346ca07: P2 M Global Theory Cech DR wedge eq  Multi 05147346ca07
-- statement:
--   The P2 M Global Theory Cech DR wedge eq  Multi 05147346ca07 construction uses the P2 M Global Theory Cech DR wedge eq  Multi 05147346ca07 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/OneFormMapEqKaehlerDifferentialMap.lean#L312-L313
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/OneFormMapEqKaehlerDifferentialMap.lean#L312-L313

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CrystallineConnectionFormCoboundaryZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_OneFormMapEqKaehlerDifferentialMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open KaehlerDifferential
open GlobalTheory GlobalTheory.CechDR
variable (R B : Type) [CommRing R] [CommRing B] [Algebra R B]
variable {R B}

theorem P2M_GlobalTheory_CechDR_wedge_eq__Multi_05147346ca07 (a b : Ω[B⁄R]) : wedge R B a b = exteriorPower.ιMulti B 2 ![a, b] := by sorry

alias «GlobalTheory».«CechDR».«wedge_eq_ιMulti» := P2M_GlobalTheory_CechDR_wedge_eq__Multi_05147346ca07
