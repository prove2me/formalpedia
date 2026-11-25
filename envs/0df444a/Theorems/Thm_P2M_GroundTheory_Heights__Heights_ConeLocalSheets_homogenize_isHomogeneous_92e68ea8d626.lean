-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeLocalSheets_homogenize_isHomogeneous_92e68ea8d626
-- name    : P2M_GroundTheory_Heights__Heights_ConeLocalSheets_homogenize_isHomogeneous_92e68ea8d626
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:36:08.378931+00:00
-- url     : https://prove2.me/theorems/a8e20ff8-5c35-4ef9-8353-a275e725c929
-- title:
--   P2 M Ground Theory Heights  Heights Cone Local Sheets homogenize is Homogeneous 92e68ea8d626: P2 M Ground Theory Heights  Heights Cone Local Sheets homogenize is Homogeneous 92e68ea8d626
-- statement:
--   The P2 M Ground Theory Heights  Heights Cone Local Sheets homogenize is Homogeneous 92e68ea8d626 construction uses the P2 M Ground Theory Heights  Heights Cone Local Sheets homogenize is Homogeneous 92e68ea8d626 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeLocalSheets.lean#L22-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeLocalSheets.lean#L22-L29

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

theorem P2M_GroundTheory_Heights__Heights_ConeLocalSheets_homogenize_isHomogeneous_92e68ea8d626 (c : MvPolynomial (Fin e) ℂ) :
    (homogenize c).IsHomogeneous c.totalDegree := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ConeLocalSheets».«homogenize_isHomogeneous» := P2M_GroundTheory_Heights__Heights_ConeLocalSheets_homogenize_isHomogeneous_92e68ea8d626
