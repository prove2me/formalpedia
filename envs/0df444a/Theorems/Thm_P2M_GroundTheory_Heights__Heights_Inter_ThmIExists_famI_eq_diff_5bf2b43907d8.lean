-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_famI_eq_diff_5bf2b43907d8
-- name    : P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_famI_eq_diff_5bf2b43907d8
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:33:13.528272+00:00
-- url     : https://prove2.me/theorems/ca887cb0-9e73-4c26-8aee-181e14bbe5ea
-- title:
--   P2 M Ground Theory Heights  Heights Inter Thm IExists fam I eq diff 5bf2b43907d8: P2 M Ground Theory Heights  Heights Inter Thm IExists fam I eq diff 5bf2b43907d8
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Thm IExists fam I eq diff 5bf2b43907d8 construction uses the P2 M Ground Theory Heights  Heights Inter Thm IExists fam I eq diff 5bf2b43907d8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ThmIExistsFamily.lean#L160-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ThmIExistsFamily.lean#L160-L177

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsMultiHomogXpow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ThmIExistsFamily
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.ThmIExists
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable (hMul : RMulStatement) {n : ℕ} (hwd : WDAt (famI (ι := ι)) n)
include hMul hwd

theorem P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_famI_eq_diff_5bf2b43907d8 {P : Ideal (MRing ι)} (hP : IsArithVar P (n + 1)) {L : Fin n → HermLine ι}
    (hL : ∀ j, IsSmoothHerm (L j)) {A C : HermLine ι} (hA : IsSmoothHerm A) (hC : IsSmoothHerm C)
    {t c : MRing ι} (ht : IsSectionOn P (A.tensor C) t) (hc : IsSectionOn P C c) :
    famI P (n + 1) (Fin.snoc L A) = recR famI P L (A.tensor C) t - recR famI P L C c := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«ThmIExists».«famI_eq_diff» := P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_famI_eq_diff_5bf2b43907d8
