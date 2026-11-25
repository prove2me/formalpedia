-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_maDens_congr_germ_60dfe05ed1fd
-- name    : P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_maDens_congr_germ_60dfe05ed1fd
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:17:04.461811+00:00
-- url     : https://prove2.me/theorems/3bc36d7e-816a-41b4-977e-130f93872e1f
-- title:
--   P2 M Ground Theory Heights  Heights Reg Lelong Annulus ma Dens congr germ 60dfe05ed1fd: P2 M Ground Theory Heights  Heights Reg Lelong Annulus ma Dens congr germ 60dfe05ed1fd
-- statement:
--   The P2 M Ground Theory Heights  Heights Reg Lelong Annulus ma Dens congr germ 60dfe05ed1fd construction uses the P2 M Ground Theory Heights  Heights Reg Lelong Annulus ma Dens congr germ 60dfe05ed1fd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L21-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L21-L31

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegRadialWeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjectionCluster
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRegLelongAnnulus
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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff
noncomputable section
open GroundTheory.Heights₂.Heights.RegLelongAnnulus
variable {n m : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin m) (Fin n) ℂ}

theorem P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_maDens_congr_germ_60dfe05ed1fd {F G : Fin m → (Fin m → ℂ) → ℝ} {y : Fin m → ℂ}
    (h : ∀ k, F k =ᶠ[𝓝 y] G k) : ReciprocityTheory.AnForm.maDens F y = ReciprocityTheory.AnForm.maDens G y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RegLelongAnnulus».«maDens_congr_germ» := P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_maDens_congr_germ_60dfe05ed1fd
