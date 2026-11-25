-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_lineFun_cover_aae3546fad86
-- name    : P2M_GroundTheory_Heights__Heights_Targets_lineFun_cover_aae3546fad86
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:45:49.517808+00:00
-- url     : https://prove2.me/theorems/434a1827-a96e-5e17-89c0-4535338944b4
-- title:
--   P2 M Ground Theory Heights  Heights Targets line Fun cover aae3546fad86: P2 M Ground Theory Heights  Heights Targets line Fun cover aae3546fad86
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets line Fun cover aae3546fad86 construction uses the P2 M Ground Theory Heights  Heights Targets line Fun cover aae3546fad86 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/StatementsConeBranchLength.lean#L76-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/StatementsConeBranchLength.lean#L76-L90

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivPushA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsDivPushMultComplex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsConeBranchLength
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial Filter Topology ReciprocityTheory.ChartRestriction.G.Geo
open GroundTheory.Heights₂.Heights.Inter

theorem P2M_GroundTheory_Heights__Heights_Targets_lineFun_cover_aae3546fad86 (v : (Σ k : Unit, PBlk 2 k) → ℂ) (hv : v ∈ Metric.ball ptZeroOne (1 / 2)) :
    ∃ t ∈ Metric.ball (0 : Fin 2 → ℂ) (1 / 2), lineFun t = v ∧ t 0 = v ⟨(), 0⟩ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«lineFun_cover» := P2M_GroundTheory_Heights__Heights_Targets_lineFun_cover_aae3546fad86
