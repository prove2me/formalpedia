-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeLocalSheets_to_mem_fibre_71799e65f6b8
-- name    : P2M_GroundTheory_Heights__Heights_ConeLocalSheets_to_mem_fibre_71799e65f6b8
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:36:12.818011+00:00
-- url     : https://prove2.me/theorems/0158ccba-4285-4ee9-9935-3183207d434e
-- title:
--   P2 M Ground Theory Heights  Heights Cone Local Sheets to mem fibre 71799e65f6b8: P2 M Ground Theory Heights  Heights Cone Local Sheets to mem fibre 71799e65f6b8
-- statement:
--   The P2 M Ground Theory Heights  Heights Cone Local Sheets to mem fibre 71799e65f6b8 construction uses the P2 M Ground Theory Heights  Heights Cone Local Sheets to mem fibre 71799e65f6b8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeLocalSheets.lean#L112-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeLocalSheets.lean#L112-L128

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

theorem P2M_GroundTheory_Heights__Heights_ConeLocalSheets_to_mem_fibre_71799e65f6b8 {P : Ideal (MRing (PBlk n))}
    {Ψ : (((k : Unit) → PBlk n k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {y : Fin e → ℂ}
    {w : ((k : Unit) → PBlk n k) → ℂ} (hw : w ∈ fibre P Ψ y) :
    ∃ z ∈ ComplexSets.fibre (chartIdeal P Ψ) (tailMat Ψ) y, segre (lift z) = w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ConeLocalSheets».«to_mem_fibre» := P2M_GroundTheory_Heights__Heights_ConeLocalSheets_to_mem_fibre_71799e65f6b8
