-- Prove2me | Theorems.Thm_P2M_PI_LocHaarRRW_isOpen_integer__dcfbdcec8b15
-- name    : P2M_PI_LocHaarRRW_isOpen_integer__dcfbdcec8b15
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:11:57.360794+00:00
-- url     : https://prove2.me/theorems/d2440a9b-f43f-45b1-a1c5-3aeaf794d519
-- title:
--   P2 M PI Loc Haar RRW is Open integer  dcfbdcec8b15: P2 M PI Loc Haar RRW is Open integer  dcfbdcec8b15
-- statement:
--   The P2 M PI Loc Haar RRW is Open integer  dcfbdcec8b15 construction uses the P2 M PI Loc Haar RRW is Open integer  dcfbdcec8b15 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalHaarSubgroup/ExistsHaarOfSubgroup.lean#L35-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalHaarSubgroup/ExistsHaarOfSubgroup.lean#L35-L35

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalHaarSubgroup_ExistsHaarOfSubgroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel MeasureTheory Topology Polynomial
open PI PI.LocHaarRRW
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem P2M_PI_LocHaarRRW_isOpen_integer__dcfbdcec8b15 : IsOpen (𝒪[K] : Set K) := by sorry

alias «PI».«LocHaarRRW».«isOpen_integer'» := P2M_PI_LocHaarRRW_isOpen_integer__dcfbdcec8b15
