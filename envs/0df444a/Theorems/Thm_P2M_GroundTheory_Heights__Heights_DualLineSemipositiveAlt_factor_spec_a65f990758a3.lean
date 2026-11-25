-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualLineSemipositiveAlt_factor_spec_a65f990758a3
-- name    : P2M_GroundTheory_Heights__Heights_DualLineSemipositiveAlt_factor_spec_a65f990758a3
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:28:46.51838+00:00
-- url     : https://prove2.me/theorems/6befa252-1757-42d0-a175-3a6b0156b8d2
-- title:
--   P2 M Ground Theory Heights  Heights Dual Line Semipositive Alt factor spec a65f990758a3: P2 M Ground Theory Heights  Heights Dual Line Semipositive Alt factor spec a65f990758a3
-- statement:
--   The P2 M Ground Theory Heights  Heights Dual Line Semipositive Alt factor spec a65f990758a3 construction uses the P2 M Ground Theory Heights  Heights Dual Line Semipositive Alt factor spec a65f990758a3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualLineSemipositive.lean#L38-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualLineSemipositive.lean#L38-L40

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLineDegreeDual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ArithModel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ADensStC
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualLineSemipositive
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
open ReciprocityTheory.ChartRestriction.G.Geo Matrix NumberField
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.DualLineSemipositiveAlt
variable {K : Type} [Field K] [NumberField K] {i : ℕ} {T : Type} [Fintype T] [DecidableEq T]

theorem P2M_GroundTheory_Heights__Heights_DualLineSemipositiveAlt_factor_spec_a65f990758a3 (F : HermLattice K i) (σ : K →+* ℂ) :
    F.metric σ = (factor F σ)ᴴ * factor F σ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«DualLineSemipositiveAlt».«factor_spec» := P2M_GroundTheory_Heights__Heights_DualLineSemipositiveAlt_factor_spec_a65f990758a3
