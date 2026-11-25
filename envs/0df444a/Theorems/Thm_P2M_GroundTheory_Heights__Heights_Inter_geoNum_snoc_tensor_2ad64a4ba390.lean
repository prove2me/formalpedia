-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_geoNum_snoc_tensor_2ad64a4ba390
-- name    : P2M_GroundTheory_Heights__Heights_Inter_geoNum_snoc_tensor_2ad64a4ba390
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:25:13.922097+00:00
-- url     : https://prove2.me/theorems/8550aef4-7277-438c-ac07-a56ec553ef57
-- title:
--   P2 M Ground Theory Heights  Heights Inter geo Num snoc tensor 2ad64a4ba390: P2 M Ground Theory Heights  Heights Inter geo Num snoc tensor 2ad64a4ba390
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter geo Num snoc tensor 2ad64a4ba390 construction uses the P2 M Ground Theory Heights  Heights Inter geo Num snoc tensor 2ad64a4ba390 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PRSlotAdd.lean#L122-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PRSlotAdd.lean#L122-L130

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
omit [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_geoNum_snoc_tensor_2ad64a4ba390 {n : ℕ} (L : Fin n → HermLine ι) (A C : HermLine ι) (W : Ideal (MRing ι)) :
    geoNum (n + 1) W (fun j => ((Fin.snoc L (A.tensor C) : Fin (n + 1) → HermLine ι) j).a) =
      geoNum (n + 1) W (fun j => ((Fin.snoc L A : Fin (n + 1) → HermLine ι) j).a) + geoNum (n + 1) W (fun j => ((Fin.snoc L C : Fin (n + 1) → HermLine ι) j).a) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«geoNum_snoc_tensor» := P2M_GroundTheory_Heights__Heights_Inter_geoNum_snoc_tensor_2ad64a4ba390
