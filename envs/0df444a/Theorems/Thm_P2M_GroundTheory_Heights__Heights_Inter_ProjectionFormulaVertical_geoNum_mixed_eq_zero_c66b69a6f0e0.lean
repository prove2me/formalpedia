-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ProjectionFormulaVertical_geoNum_mixed_eq_zero_c66b69a6f0e0
-- name    : P2M_GroundTheory_Heights__Heights_Inter_ProjectionFormulaVertical_geoNum_mixed_eq_zero_c66b69a6f0e0
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:43:14.474922+00:00
-- url     : https://prove2.me/theorems/39ae726b-c61e-4ca4-a5c0-ee3ca4ffd382
-- title:
--   P2 M Ground Theory Heights  Heights Inter Projection Formula Vertical geo Num mixed eq zero c66b69a6f0e0: P2 M Ground Theory Heights  Heights Inter Projection Formula Vertical geo Num mixed eq zero c6
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Projection Formula Vertical geo Num mixed eq zero c66b69a6f0e0 construction uses the P2 M Ground Theory Heights  Heights Inter Projection Formula Vertical geo Num mixed eq zero c66b69a6f0e0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PPFVert.lean#L19-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PPFVert.lean#L19-L62

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsUniqueStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MixedFieldContraction_ContractMixedFieldStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsPFVert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsMultiProjPrimeImageZ
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFVert
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.Inter.ProjectionFormulaVertical
open PointVertical

theorem P2M_GroundTheory_Heights__Heights_Inter_ProjectionFormulaVertical_geoNum_mixed_eq_zero_c66b69a6f0e0
    (hGeo : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)], GeoNumStatement ι)
    (hR4 : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)],
      ExistsUniqueStatement F ι)
    (hCMF : ContractMixedFieldStatement)
    {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
    {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v) {P' : Ideal (MRing ι')} {d r : ℕ}
    (hP : IsArithVar (imageZ v P') d) {W : Ideal (MRing ι')} (hPW : P' ≤ W)
    (hWm : IsMultiProjPrime W) (hpr : (charOf W).Prime)
    (hWd : ringKrullDim (MRing ι' ⧸ W) = ((d + r + Fintype.card K' : ℕ) : WithBot ℕ∞))
    (L : Fin d → K → ℤ) (N : Fin r → K' → ℤ) :
    geoNum (d + r) W (Fin.append (fun j => pullDeg κ (L j)) N) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«ProjectionFormulaVertical».«geoNum_mixed_eq_zero» := P2M_GroundTheory_Heights__Heights_Inter_ProjectionFormulaVertical_geoNum_mixed_eq_zero_c66b69a6f0e0
