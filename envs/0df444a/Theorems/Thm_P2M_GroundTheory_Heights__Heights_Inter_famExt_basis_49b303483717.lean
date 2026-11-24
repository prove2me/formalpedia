-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_famExt_basis_49b303483717
-- name    : P2M_GroundTheory_Heights__Heights_Inter_famExt_basis_49b303483717
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:33:23.629533+00:00
-- url     : https://prove2.me/theorems/1586e5e5-e292-4089-a69e-dcb59077a2e0
-- title:
--   P2 M Ground Theory Heights  Heights Inter fam Ext basis 49b303483717: P2 M Ground Theory Heights  Heights Inter fam Ext basis 49b303483717
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter fam Ext basis 49b303483717 construction uses the P2 M Ground Theory Heights  Heights Inter fam Ext basis 49b303483717 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PThmAExpand.lean#L57-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PThmAExpand.lean#L57-L68

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_SymExp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsAntisym
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PThmAExpand
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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I2
noncomputable section
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ} {P : Ideal (MRing ι)} {n : ℕ}
omit [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_famExt_basis_49b303483717 (e : Fin 2 → HermLine ι) (t : Fin n → Fin 2) :
    famExt I P n e (fun j => Pi.single (t j) 1) = I P n (e ∘ t) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«famExt_basis» := P2M_GroundTheory_Heights__Heights_Inter_famExt_basis_49b303483717
