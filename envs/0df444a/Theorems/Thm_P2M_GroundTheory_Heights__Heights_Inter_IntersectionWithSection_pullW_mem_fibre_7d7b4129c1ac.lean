-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_IntersectionWithSection_pullW_mem_fibre_7d7b4129c1ac
-- name    : P2M_GroundTheory_Heights__Heights_Inter_IntersectionWithSection_pullW_mem_fibre_7d7b4129c1ac
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:32:38.554799+00:00
-- url     : https://prove2.me/theorems/1958208f-e0ed-5802-b2c9-d7d36ec79823
-- title:
--   P2 M Ground Theory Heights  Heights Inter Intersection With Section pull W mem fibre 7d7b4129c1ac: P2 M Ground Theory Heights  Heights Inter Intersection With Section pull W mem fibre 7d7b4129c1ac
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Intersection With Section pull W mem fibre 7d7b4129c1ac construction uses the P2 M Ground Theory Heights  Heights Inter Intersection With Section pull W mem fibre 7d7b4129c1ac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PullWMemFibre.lean#L37-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PullWMemFibre.lean#L37-L58

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridge
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedE
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PtsIntegralLogNormRat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsFurtherFurther
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsFurtherExtra
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PullWMemFibre
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M
open GroundTheory.Heights₂.Heights.Inter.IntersectionWithSection
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_IntersectionWithSection_pullW_mem_fibre_7d7b4129c1ac {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {P' J' : Ideal (MRing ι')} {n : ℕ} (hP : IsArithVar (imageZ v P') (n + 1)) (R : AnLogRes P' J' n)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) {x : R.X}
    (h0 : Ψ (segre (pullPt R v x)) 0 ≠ 0) : pullW R v Ψ x ∈ fibre (imageZ v P') Ψ (pullQ R v Ψ x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«IntersectionWithSection».«pullW_mem_fibre» := P2M_GroundTheory_Heights__Heights_Inter_IntersectionWithSection_pullW_mem_fibre_7d7b4129c1ac
