-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeLocalSheets_eq_cons_b295b14b7ef8
-- name    : P2M_GroundTheory_Heights__Heights_ConeLocalSheets_eq_cons_b295b14b7ef8
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:20:18.568899+00:00
-- url     : https://prove2.me/theorems/ddce110c-5520-5405-92bc-6e180f700e86
-- title:
--   P2 M Ground Theory Heights  Heights Cone Local Sheets eq cons b295b14b7ef8: P2 M Ground Theory Heights  Heights Cone Local Sheets eq cons b295b14b7ef8
-- statement:
--   The P2 M Ground Theory Heights  Heights Cone Local Sheets eq cons b295b14b7ef8 construction uses the P2 M Ground Theory Heights  Heights Cone Local Sheets eq cons b295b14b7ef8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeLocalSheets.lean#L87-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeLocalSheets.lean#L87-L92

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

theorem P2M_GroundTheory_Heights__Heights_ConeLocalSheets_eq_cons_b295b14b7ef8 {v : Fin (e + 1) → ℂ} {y : Fin e → ℂ} (h0 : v 0 = 1) (hs : ∀ i, v i.succ = y i) :
    v = Fin.cons 1 y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ConeLocalSheets».«eq_cons» := P2M_GroundTheory_Heights__Heights_ConeLocalSheets_eq_cons_b295b14b7ef8
