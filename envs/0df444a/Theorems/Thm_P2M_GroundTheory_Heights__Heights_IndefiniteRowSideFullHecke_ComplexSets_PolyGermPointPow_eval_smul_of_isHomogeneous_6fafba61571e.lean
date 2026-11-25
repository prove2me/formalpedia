-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PolyGermPointPow_eval_smul_of_isHomogeneous_6fafba61571e
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PolyGermPointPow_eval_smul_of_isHomogeneous_6fafba61571e
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:20:52.267652+00:00
-- url     : https://prove2.me/theorems/bb456cfd-2bd0-4014-8845-f175d9b9ec66
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Poly Germ Point Pow eval smul of is Homogeneous 6fafba61571e: P2 M Ground Theory Heights  Heights Indefinite Row Side Fu
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Poly Germ Point Pow eval smul of is Homogeneous 6fafba61571e construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Poly Germ Point Pow eval smul of is Homogeneous 6fafba61571e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPolyGermPointPow.lean#L41-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPolyGermPointPow.lean#L41-L43

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StZariskiObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPolyGermPointPow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_GradientAtPoint
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_EvalSmulOfIsHomogeneous
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPolyGermPointPow
import Theorems.Thm_UpperTheory_Reformulated_B_HomogeneousEvalSmul_eval_smul_of_isHomogeneous

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MvPolynomial Topology Filter Asymptotics
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.PolyGermPointPow

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PolyGermPointPow_eval_smul_of_isHomogeneous_6fafba61571e {σ : Type} [Fintype σ] {h : MvPolynomial σ ℂ} {d : ℕ}
    (hh : h.IsHomogeneous d) (t : ℂ) (v : σ → ℂ) : eval (t • v) h = t ^ d * eval v h := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«PolyGermPointPow».«eval_smul_of_isHomogeneous» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PolyGermPointPow_eval_smul_of_isHomogeneous_6fafba61571e
