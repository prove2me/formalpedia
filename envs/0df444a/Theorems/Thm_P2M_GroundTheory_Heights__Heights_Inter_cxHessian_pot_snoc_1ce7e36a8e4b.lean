-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_cxHessian_pot_snoc_1ce7e36a8e4b
-- name    : P2M_GroundTheory_Heights__Heights_Inter_cxHessian_pot_snoc_1ce7e36a8e4b
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:36:51.60443+00:00
-- url     : https://prove2.me/theorems/30a15e08-54ae-5732-a095-02e5901be354
-- title:
--   P2 M Ground Theory Heights  Heights Inter cx Hessian pot snoc 1ce7e36a8e4b: P2 M Ground Theory Heights  Heights Inter cx Hessian pot snoc 1ce7e36a8e4b
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter cx Hessian pot snoc 1ce7e36a8e4b construction uses the P2 M Ground Theory Heights  Heights Inter cx Hessian pot snoc 1ce7e36a8e4b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PRSlotAdd.lean#L36-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PRSlotAdd.lean#L36-L46

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AMixSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsWellDefined
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRSlotAdd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory Filter
open scoped Topology ContDiff
noncomputable section
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_cxHessian_pot_snoc_1ce7e36a8e4b {n : ℕ} (L : Fin n → HermLine ι) (A X : HermLine ι)
    (γ : (Fin (n + 1) → ℂ) → (Σ k, ι k) → ℂ) (y : Fin (n + 1) → ℂ) :
    (fun k => cxHessian (fun y' => pot (Fin.snoc L X) k (γ y')) y) =
      Function.update (fun k => cxHessian (fun y' => pot (Fin.snoc L A) k (γ y')) y) (Fin.last n)
        (cxHessian (fun y' => Real.log (X.h (γ y'))) y) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«cxHessian_pot_snoc» := P2M_GroundTheory_Heights__Heights_Inter_cxHessian_pot_snoc_1ce7e36a8e4b
