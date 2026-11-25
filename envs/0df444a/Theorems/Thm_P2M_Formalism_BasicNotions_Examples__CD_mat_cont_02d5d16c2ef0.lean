-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_mat_cont_02d5d16c2ef0
-- name    : P2M_Formalism_BasicNotions_Examples__CD_mat_cont_02d5d16c2ef0
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T16:16:49.207871+00:00
-- url     : https://prove2.me/theorems/623f19c1-37f0-4405-ae11-24d3640bdf85
-- title:
--   P2 M Formalism Basic Notions Examples  CD mat cont 02d5d16c2ef0: P2 M Formalism Basic Notions Examples  CD mat cont 02d5d16c2ef0
-- statement:
--   The P2 M Formalism Basic Notions Examples  CD mat cont 02d5d16c2ef0 construction uses the P2 M Formalism Basic Notions Examples  CD mat cont 02d5d16c2ef0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/HaarDensityNeZero.lean#L45-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/HaarDensityNeZero.lean#L45-L45

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_ExistsDensity
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_ExistsOmegaLeb
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NormLeSum
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_HaarDensityNeZero
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
open MeasureTheory Filter Topology Metric NormedSpace Set Matrix Formalism.UG.P
open scoped ENNReal NNReal Matrix.Norms.Operator
variable (P Q : ℕ)
local notation "J" => Formalism.UG.Jpq P Q

theorem P2M_Formalism_BasicNotions_Examples__CD_mat_cont_02d5d16c2ef0 : Continuous (UpqT.mat : UpqT P Q → MM P Q) := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«CD».«mat_cont» := P2M_Formalism_BasicNotions_Examples__CD_mat_cont_02d5d16c2ef0
