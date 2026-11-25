-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_arInt_snoc_tensor_66e94ac2868a
-- name    : P2M_GroundTheory_Heights__Heights_Inter_arInt_snoc_tensor_66e94ac2868a
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:26:05.609196+00:00
-- url     : https://prove2.me/theorems/30067bf4-97bd-487c-aed5-8721d6deaf10
-- title:
--   P2 M Ground Theory Heights  Heights Inter ar Int snoc tensor 66e94ac2868a: P2 M Ground Theory Heights  Heights Inter ar Int snoc tensor 66e94ac2868a
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter ar Int snoc tensor 66e94ac2868a construction uses the P2 M Ground Theory Heights  Heights Inter ar Int snoc tensor 66e94ac2868a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PRSlotAdd.lean#L93-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PRSlotAdd.lean#L93-L118

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

theorem P2M_GroundTheory_Heights__Heights_Inter_arInt_snoc_tensor_66e94ac2868a (hFF : FibreFiniteStatement) (hInt : PtsIntegrableStatement)
    {P : Ideal (MRing ι)} {n : ℕ} (L : Fin n → HermLine ι) {A C B : HermLine ι} {s : MRing ι}
    (hP : IsArithVar P (n + 2)) (hL : ∀ j, IsSmoothHerm (L j)) (hA : IsSmoothHerm A)
    (hC : IsSmoothHerm C) (hB : IsSmoothHerm B) (hs : IsSectionOn P B s) :
    arInt P s B (Fin.snoc L (A.tensor C)) =
      arInt P s B (Fin.snoc L A) + arInt P s B (Fin.snoc L C) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«arInt_snoc_tensor» := P2M_GroundTheory_Heights__Heights_Inter_arInt_snoc_tensor_66e94ac2868a
