-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isProjVarQ_of_isArithVar_5640a3c8ef08
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isProjVarQ_of_isArithVar_5640a3c8ef08
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T16:01:15.459713+00:00
-- url     : https://prove2.me/theorems/5f5e600c-cd11-4f2a-bd0c-042d715f117f
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter is Proj Var Q of is Arith Var 5640a3c8ef08: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter is Proj Va
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter is Proj Var Q of is Arith Var 5640a3c8ef08 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter is Proj Var Q of is Arith Var 5640a3c8ef08 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsSmoothMetricOfIsSmoothHerm.lean#L43-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsSmoothMetricOfIsSmoothHerm.lean#L43-L88

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AnalyticResolutionHypothesesProjectiveLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisorAlt
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsSmoothMetricOfIsSmoothHerm
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
open MvPolynomial
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing)
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isProjVarQ_of_isArithVar_5640a3c8ef08 {P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing ι)} {e : ℕ}
    (hP : ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar P (e + 1)) :
    IsProjVarQ (P.map (MvPolynomial.map (Int.castRingHom ℚ))) e := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«isProjVarQ_of_isArithVar» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isProjVarQ_of_isArithVar_5640a3c8ef08
