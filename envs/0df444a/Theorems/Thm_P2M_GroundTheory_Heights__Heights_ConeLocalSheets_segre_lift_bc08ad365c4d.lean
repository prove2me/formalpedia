-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeLocalSheets_segre_lift_bc08ad365c4d
-- name    : P2M_GroundTheory_Heights__Heights_ConeLocalSheets_segre_lift_bc08ad365c4d
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:59:35.176262+00:00
-- url     : https://prove2.me/theorems/2e6e3b2b-484a-4289-aa73-b42a29e5ae93
-- title:
--   P2 M Ground Theory Heights  Heights Cone Local Sheets segre lift bc08ad365c4d: P2 M Ground Theory Heights  Heights Cone Local Sheets segre lift bc08ad365c4d
-- statement:
--   The P2 M Ground Theory Heights  Heights Cone Local Sheets segre lift bc08ad365c4d construction uses the P2 M Ground Theory Heights  Heights Cone Local Sheets segre lift bc08ad365c4d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeLocalSheets.lean#L52-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeLocalSheets.lean#L52-L54

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeLocalSheets
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsQuasiFiniteSheets
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeLocalSheets
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj mcPts fibre segre)
open Matrix
open GroundTheory.Heights₂.Heights.ConeLocalSheets
variable {n e : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ConeLocalSheets_segre_lift_bc08ad365c4d (z : Fin n → ℂ) : segre (lift z) = fun i => z (i ()) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ConeLocalSheets».«segre_lift» := P2M_GroundTheory_Heights__Heights_ConeLocalSheets_segre_lift_bc08ad365c4d
