-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeLocalSheets_homogenize_ne_zero_b4aa12b26ec4
-- name    : P2M_GroundTheory_Heights__Heights_ConeLocalSheets_homogenize_ne_zero_b4aa12b26ec4
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:23:50.234455+00:00
-- url     : https://prove2.me/theorems/354402d9-2dca-51ea-a993-93259a08afbb
-- title:
--   P2 M Ground Theory Heights  Heights Cone Local Sheets homogenize ne zero b4aa12b26ec4: P2 M Ground Theory Heights  Heights Cone Local Sheets homogenize ne zero b4aa12b26ec4
-- statement:
--   The P2 M Ground Theory Heights  Heights Cone Local Sheets homogenize ne zero b4aa12b26ec4 construction uses the P2 M Ground Theory Heights  Heights Cone Local Sheets homogenize ne zero b4aa12b26ec4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeLocalSheets.lean#L38-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeLocalSheets.lean#L38-L45

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

theorem P2M_GroundTheory_Heights__Heights_ConeLocalSheets_homogenize_ne_zero_b4aa12b26ec4 {c : MvPolynomial (Fin e) ℂ} (hc : c ≠ 0) : homogenize c ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ConeLocalSheets».«homogenize_ne_zero» := P2M_GroundTheory_Heights__Heights_ConeLocalSheets_homogenize_ne_zero_b4aa12b26ec4
