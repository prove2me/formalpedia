-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_sheetDensity_snoc_tensor_a4bd3751e1b3
-- name    : P2M_GroundTheory_Heights__Heights_Inter_sheetDensity_snoc_tensor_a4bd3751e1b3
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:36:11.840639+00:00
-- url     : https://prove2.me/theorems/4024397e-5d42-4ea8-9f8b-2537183f11a9
-- title:
--   P2 M Ground Theory Heights  Heights Inter sheet Density snoc tensor a4bd3751e1b3: P2 M Ground Theory Heights  Heights Inter sheet Density snoc tensor a4bd3751e1b3
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter sheet Density snoc tensor a4bd3751e1b3 construction uses the P2 M Ground Theory Heights  Heights Inter sheet Density snoc tensor a4bd3751e1b3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PRSlotAdd.lean#L78-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PRSlotAdd.lean#L78-L91

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

theorem P2M_GroundTheory_Heights__Heights_Inter_sheetDensity_snoc_tensor_a4bd3751e1b3 (P : Ideal (MRing ι)) {n : ℕ}
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1 + 1) → ℂ)) (L : Fin n → HermLine ι)
    {A C : HermLine ι} (hA : IsSmoothHerm A) (hC : IsSmoothHerm C) (g : ((Σ k, ι k) → ℂ) → ℝ)
    (y : Fin (n + 1) → ℂ) (w : ((k : K) → ι k) → ℂ) :
    sheetDensity P Ψ (pot (Fin.snoc L (A.tensor C))) g y w =
      sheetDensity P Ψ (pot (Fin.snoc L A)) g y w + sheetDensity P Ψ (pot (Fin.snoc L C)) g y w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«sheetDensity_snoc_tensor» := P2M_GroundTheory_Heights__Heights_Inter_sheetDensity_snoc_tensor_a4bd3751e1b3
