-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeLocalSheets_fibre_finite_e6f7d229a02e
-- name    : P2M_GroundTheory_Heights__Heights_ConeLocalSheets_fibre_finite_e6f7d229a02e
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:37:45.382947+00:00
-- url     : https://prove2.me/theorems/5942407e-92e8-495a-aeb2-40b31de08e87
-- title:
--   P2 M Ground Theory Heights  Heights Cone Local Sheets fibre finite e6f7d229a02e: P2 M Ground Theory Heights  Heights Cone Local Sheets fibre finite e6f7d229a02e
-- statement:
--   The P2 M Ground Theory Heights  Heights Cone Local Sheets fibre finite e6f7d229a02e construction uses the P2 M Ground Theory Heights  Heights Cone Local Sheets fibre finite e6f7d229a02e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeLocalSheets.lean#L130-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeLocalSheets.lean#L130-L141

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

theorem P2M_GroundTheory_Heights__Heights_ConeLocalSheets_fibre_finite_e6f7d229a02e {P : Ideal (MRing (PBlk n))}
    {Ψ : (((k : Unit) → PBlk n k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} (hP : IsArithVar P (e + 1))
    (hΨ : IsGoodProj P Ψ) (y : Fin e → ℂ) :
    (ComplexSets.fibre (chartIdeal P Ψ) (tailMat Ψ) y).Finite := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ConeLocalSheets».«fibre_finite» := P2M_GroundTheory_Heights__Heights_ConeLocalSheets_fibre_finite_e6f7d229a02e
