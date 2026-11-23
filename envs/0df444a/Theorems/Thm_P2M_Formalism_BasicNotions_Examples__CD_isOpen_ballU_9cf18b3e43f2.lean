-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_isOpen_ballU_9cf18b3e43f2
-- name    : P2M_Formalism_BasicNotions_Examples__CD_isOpen_ballU_9cf18b3e43f2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:01:59.301199+00:00
-- url     : https://prove2.me/theorems/0e400e3f-a1b5-42e0-830b-ffbdcdf772da
-- title:
--   P2 M Formalism Basic Notions Examples  CD is Open ball U 9cf18b3e43f2: P2 M Formalism Basic Notions Examples  CD is Open ball U 9cf18b3e43f2
-- statement:
--   The P2 M Formalism Basic Notions Examples  CD is Open ball U 9cf18b3e43f2 construction uses the P2 M Formalism Basic Notions Examples  CD is Open ball U 9cf18b3e43f2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/ExistsOmegaLeb.lean#L167-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/ExistsOmegaLeb.lean#L167-L171

import Definitions.Def_Formalism_LocalRingCardinality_DataCD
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Upqcpt
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_ExistsOmegaLeb
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.CD
open MeasureTheory Filter Topology Set Matrix Formalism.UG.P
open scoped ENNReal NNReal
variable (P Q : ℕ)
local notation "J" => Formalism.UG.Jpq P Q

theorem P2M_Formalism_BasicNotions_Examples__CD_isOpen_ballU_9cf18b3e43f2 (r : ℝ) : IsOpen (ballU P Q r) := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«CD».«isOpen_ballU» := P2M_Formalism_BasicNotions_Examples__CD_isOpen_ballU_9cf18b3e43f2
