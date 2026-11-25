-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeLocalSheets_lift_injective_4da4e73bfd03
-- name    : P2M_GroundTheory_Heights__Heights_ConeLocalSheets_lift_injective_4da4e73bfd03
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:17:56.242961+00:00
-- url     : https://prove2.me/theorems/bb7ab32f-ec17-4e19-91fb-6718f8fe8e6d
-- title:
--   P2 M Ground Theory Heights  Heights Cone Local Sheets lift injective 4da4e73bfd03: P2 M Ground Theory Heights  Heights Cone Local Sheets lift injective 4da4e73bfd03
-- statement:
--   The P2 M Ground Theory Heights  Heights Cone Local Sheets lift injective 4da4e73bfd03 construction uses the P2 M Ground Theory Heights  Heights Cone Local Sheets lift injective 4da4e73bfd03 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeLocalSheets.lean#L49-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeLocalSheets.lean#L49-L50

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

theorem P2M_GroundTheory_Heights__Heights_ConeLocalSheets_lift_injective_4da4e73bfd03 : Function.Injective (lift : (Fin n → ℂ) → (Σ k, PBlk n k) → ℂ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ConeLocalSheets».«lift_injective» := P2M_GroundTheory_Heights__Heights_ConeLocalSheets_lift_injective_4da4e73bfd03
