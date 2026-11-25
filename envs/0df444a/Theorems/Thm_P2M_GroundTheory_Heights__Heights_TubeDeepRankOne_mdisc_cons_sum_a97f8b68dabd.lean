-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_TubeDeepRankOne_mdisc_cons_sum_a97f8b68dabd
-- name    : P2M_GroundTheory_Heights__Heights_TubeDeepRankOne_mdisc_cons_sum_a97f8b68dabd
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:42:29.695187+00:00
-- url     : https://prove2.me/theorems/98cfed39-4935-4e9b-81ce-87fc6763ee55
-- title:
--   P2 M Ground Theory Heights  Heights Tube Deep Rank One mdisc cons sum a97f8b68dabd: P2 M Ground Theory Heights  Heights Tube Deep Rank One mdisc cons sum a97f8b68dabd
-- statement:
--   The P2 M Ground Theory Heights  Heights Tube Deep Rank One mdisc cons sum a97f8b68dabd construction uses the P2 M Ground Theory Heights  Heights Tube Deep Rank One mdisc cons sum a97f8b68dabd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PTubeDeepRankOne.lean#L41-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PTubeDeepRankOne.lean#L41-L49

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCIsHermitian
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMaDensLeibniz
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTubeDeepRankOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PTubeDeepRankOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial Matrix ComplexSets ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A Filter Topology
noncomputable section
open GroundTheory.Heights₂.Heights.TubeDeepRankOne

theorem P2M_GroundTheory_Heights__Heights_TubeDeepRankOne_mdisc_cons_sum_a97f8b68dabd {d n : ℕ} (A₀ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (B : Fin n → Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :
    mdisc (Fin.cons A₀ (fun _ => ∑ m, B m) : Fin (d + 1) → Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) =
      ∑ I : Fin d → Fin n,
        mdisc (Fin.cons A₀ (fun i => B (I i)) : Fin (d + 1) → Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«TubeDeepRankOne».«mdisc_cons_sum» := P2M_GroundTheory_Heights__Heights_TubeDeepRankOne_mdisc_cons_sum_a97f8b68dabd
