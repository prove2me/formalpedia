-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagDim_diagProd_succ_7d2c690099e9
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagDim_diagProd_succ_7d2c690099e9
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T02:05:16.142425+00:00
-- url     : https://prove2.me/theorems/20b6d656-5cb2-4d60-a9df-c454f77e722f
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Flag Dim diag Prod succ 7d2c690099e9: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Flag Dim diag Pr
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Flag Dim diag Prod succ 7d2c690099e9 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Flag Dim diag Prod succ 7d2c690099e9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFlagDim.lean#L286-L289
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFlagDim.lean#L286-L289

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FlagDimSt
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagDim
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagDim
variable (F : Type) [Field F] (n : ℕ)

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagDim_diagProd_succ_7d2c690099e9 (i : ℕ) (h : i + 1 < n) :
    diagProd F n (i + 1) h = diagProd F n i (by omega) * uMat F n ⟨i, by omega⟩ ⟨i, by omega⟩ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«FlagDim».«diagProd_succ» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagDim_diagProd_succ_7d2c690099e9
