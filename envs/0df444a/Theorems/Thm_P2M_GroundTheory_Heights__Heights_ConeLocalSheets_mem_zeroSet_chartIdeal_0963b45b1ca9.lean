-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeLocalSheets_mem_zeroSet_chartIdeal_0963b45b1ca9
-- name    : P2M_GroundTheory_Heights__Heights_ConeLocalSheets_mem_zeroSet_chartIdeal_0963b45b1ca9
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:59:07.678034+00:00
-- url     : https://prove2.me/theorems/ee39c035-a6e2-4067-b488-eda5c40a1f03
-- title:
--   P2 M Ground Theory Heights  Heights Cone Local Sheets mem zero Set chart Ideal 0963b45b1ca9: P2 M Ground Theory Heights  Heights Cone Local Sheets mem zero Set chart Ideal 0963b45b1ca9
-- statement:
--   The P2 M Ground Theory Heights  Heights Cone Local Sheets mem zero Set chart Ideal 0963b45b1ca9 construction uses the P2 M Ground Theory Heights  Heights Cone Local Sheets mem zero Set chart Ideal 0963b45b1ca9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeLocalSheets.lean#L72-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeLocalSheets.lean#L72-L85

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

theorem P2M_GroundTheory_Heights__Heights_ConeLocalSheets_mem_zeroSet_chartIdeal_0963b45b1ca9 {P : Ideal (MRing (PBlk n))}
    {Ψ : (((k : Unit) → PBlk n k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {z : Fin n → ℂ} :
    z ∈ ComplexSets.zeroSet (chartIdeal P Ψ) ↔
      (∀ f ∈ P, eval (lift z) (map (Int.castRingHom ℂ) f) = 0) ∧ Ψ (segre (lift z)) 0 = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ConeLocalSheets».«mem_zeroSet_chartIdeal» := P2M_GroundTheory_Heights__Heights_ConeLocalSheets_mem_zeroSet_chartIdeal_0963b45b1ca9
