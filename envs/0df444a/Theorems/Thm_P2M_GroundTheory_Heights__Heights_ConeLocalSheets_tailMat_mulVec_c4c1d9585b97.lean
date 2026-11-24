-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeLocalSheets_tailMat_mulVec_c4c1d9585b97
-- name    : P2M_GroundTheory_Heights__Heights_ConeLocalSheets_tailMat_mulVec_c4c1d9585b97
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:59:35.972175+00:00
-- url     : https://prove2.me/theorems/6c63a047-6468-492d-b111-3be5a514d68b
-- title:
--   P2 M Ground Theory Heights  Heights Cone Local Sheets tail Mat mul Vec c4c1d9585b97: P2 M Ground Theory Heights  Heights Cone Local Sheets tail Mat mul Vec c4c1d9585b97
-- statement:
--   The P2 M Ground Theory Heights  Heights Cone Local Sheets tail Mat mul Vec c4c1d9585b97 construction uses the P2 M Ground Theory Heights  Heights Cone Local Sheets tail Mat mul Vec c4c1d9585b97 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeLocalSheets.lean#L94-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeLocalSheets.lean#L94-L97

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

theorem P2M_GroundTheory_Heights__Heights_ConeLocalSheets_tailMat_mulVec_c4c1d9585b97 (Ψ : (((k : Unit) → PBlk n k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (z : Fin n → ℂ)
    (i : Fin e) : (tailMat Ψ *ᵥ z) i = Ψ (segre (lift z)) i.succ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ConeLocalSheets».«tailMat_mulVec» := P2M_GroundTheory_Heights__Heights_ConeLocalSheets_tailMat_mulVec_c4c1d9585b97
