-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_mat_left_inv_4e578481c43f
-- name    : P2M_Formalism_BasicNotions_Examples__CD_mat_left_inv_4e578481c43f
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T16:17:16.077304+00:00
-- url     : https://prove2.me/theorems/172a266b-9f8d-4206-96ee-6b80579233ae
-- title:
--   P2 M Formalism Basic Notions Examples  CD mat left inv 4e578481c43f: P2 M Formalism Basic Notions Examples  CD mat left inv 4e578481c43f
-- statement:
--   The P2 M Formalism Basic Notions Examples  CD mat left inv 4e578481c43f construction uses the P2 M Formalism Basic Notions Examples  CD mat left inv 4e578481c43f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/HaarDensityNeZero.lean#L25-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/HaarDensityNeZero.lean#L25-L29

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

theorem P2M_Formalism_BasicNotions_Examples__CD_mat_left_inv_4e578481c43f (g : UpqT P Q) : (J * (UpqT.mat g)ᴴ * J) * UpqT.mat g = 1 := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«CD».«mat_left_inv» := P2M_Formalism_BasicNotions_Examples__CD_mat_left_inv_4e578481c43f
