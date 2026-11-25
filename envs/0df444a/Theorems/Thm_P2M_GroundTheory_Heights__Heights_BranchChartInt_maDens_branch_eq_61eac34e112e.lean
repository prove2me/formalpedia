-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_BranchChartInt_maDens_branch_eq_61eac34e112e
-- name    : P2M_GroundTheory_Heights__Heights_BranchChartInt_maDens_branch_eq_61eac34e112e
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:16:31.254682+00:00
-- url     : https://prove2.me/theorems/a487382c-e22a-47b6-8347-04037437e467
-- title:
--   P2 M Ground Theory Heights  Heights Branch Chart Int ma Dens branch eq 61eac34e112e: P2 M Ground Theory Heights  Heights Branch Chart Int ma Dens branch eq 61eac34e112e
-- statement:
--   The P2 M Ground Theory Heights  Heights Branch Chart Int ma Dens branch eq 61eac34e112e construction uses the P2 M Ground Theory Heights  Heights Branch Chart Int ma Dens branch eq 61eac34e112e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PBranchChartInt.lean#L64-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PBranchChartInt.lean#L64-L103

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchChartInt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHolomorphicFibreSumInt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchSheetAE
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_OsgoodSeparate
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PBranchChartInt
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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets ReciprocityTheory.AnForm.A
open scoped ContDiff
noncomputable section
open GroundTheory.Heights₂.Heights.BranchChartInt

theorem P2M_GroundTheory_Heights__Heights_BranchChartInt_maDens_branch_eq_61eac34e112e {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    {p : Fin n → ℂ} (γ : VarBranch J d p) {φ : Fin d → (Fin n → ℂ) → ℝ}
    (hφ : ∀ k, SmoothNear (zeroSet J) (φ k)) {t : Fin d → ℂ} (ht : t ∈ Metric.ball (0 : Fin d → ℂ) γ.radius)
    {s : (Fin d → ℂ) → Fin n → ℂ} (hs : IsSheetAt J A (γ.toFun t) s) :
    ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ γ.toFun) t =
      ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) (A *ᵥ γ.toFun t) *
        Complex.normSq (jacC (fun t => A *ᵥ γ.toFun t) t).det := by sorry

alias «GroundTheory».«Heights₂».«Heights».«BranchChartInt».«maDens_branch_eq» := P2M_GroundTheory_Heights__Heights_BranchChartInt_maDens_branch_eq_61eac34e112e
