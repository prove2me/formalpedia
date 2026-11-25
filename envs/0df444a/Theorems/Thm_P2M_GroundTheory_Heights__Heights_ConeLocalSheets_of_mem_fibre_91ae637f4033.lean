-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeLocalSheets_of_mem_fibre_91ae637f4033
-- name    : P2M_GroundTheory_Heights__Heights_ConeLocalSheets_of_mem_fibre_91ae637f4033
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:59:46.861626+00:00
-- url     : https://prove2.me/theorems/caa80892-1649-4b42-ac52-d0d3f7a41a57
-- title:
--   P2 M Ground Theory Heights  Heights Cone Local Sheets of mem fibre 91ae637f4033: P2 M Ground Theory Heights  Heights Cone Local Sheets of mem fibre 91ae637f4033
-- statement:
--   The P2 M Ground Theory Heights  Heights Cone Local Sheets of mem fibre 91ae637f4033 construction uses the P2 M Ground Theory Heights  Heights Cone Local Sheets of mem fibre 91ae637f4033 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeLocalSheets.lean#L99-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeLocalSheets.lean#L99-L110

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

theorem P2M_GroundTheory_Heights__Heights_ConeLocalSheets_of_mem_fibre_91ae637f4033 {P : Ideal (MRing (PBlk n))}
    {Ψ : (((k : Unit) → PBlk n k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {y : Fin e → ℂ} {z : Fin n → ℂ}
    (hz : z ∈ ComplexSets.fibre (chartIdeal P Ψ) (tailMat Ψ) y) :
    lift z ∈ mcPts P ∧ Ψ (segre (lift z)) = Fin.cons 1 y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ConeLocalSheets».«of_mem_fibre» := P2M_GroundTheory_Heights__Heights_ConeLocalSheets_of_mem_fibre_91ae637f4033
