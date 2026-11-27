-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_exp_mul_neg__d0646542b8d7
-- name    : P2M_Formalism_BasicNotions_Examples__CD_exp_mul_neg__d0646542b8d7
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T16:16:32.184328+00:00
-- url     : https://prove2.me/theorems/4ff6c2b8-f5bc-51ee-b626-358baf0f2743
-- title:
--   P2 M Formalism Basic Notions Examples  CD exp mul neg  d0646542b8d7: P2 M Formalism Basic Notions Examples  CD exp mul neg  d0646542b8d7
-- statement:
--   The P2 M Formalism Basic Notions Examples  CD exp mul neg  d0646542b8d7 construction uses the P2 M Formalism Basic Notions Examples  CD exp mul neg  d0646542b8d7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/HaarDensityNeZero.lean#L89-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/HaarDensityNeZero.lean#L89-L92

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

theorem P2M_Formalism_BasicNotions_Examples__CD_exp_mul_neg__d0646542b8d7 (X : MM P Q) : exp X * exp (-X) = 1 := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«CD».«exp_mul_neg'» := P2M_Formalism_BasicNotions_Examples__CD_exp_mul_neg__d0646542b8d7
