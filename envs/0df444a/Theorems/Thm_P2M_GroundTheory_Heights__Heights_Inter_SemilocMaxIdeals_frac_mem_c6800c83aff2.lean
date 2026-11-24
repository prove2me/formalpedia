-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_SemilocMaxIdeals_frac_mem_c6800c83aff2
-- name    : P2M_GroundTheory_Heights__Heights_Inter_SemilocMaxIdeals_frac_mem_c6800c83aff2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:03:58.737177+00:00
-- url     : https://prove2.me/theorems/dbeea376-2069-4a81-ba00-1db03d3cd8ed
-- title:
--   P2 M Ground Theory Heights  Heights Inter Semiloc Max Ideals frac mem c6800c83aff2: P2 M Ground Theory Heights  Heights Inter Semiloc Max Ideals frac mem c6800c83aff2
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Semiloc Max Ideals frac mem c6800c83aff2 construction uses the P2 M Ground Theory Heights  Heights Inter Semiloc Max Ideals frac mem c6800c83aff2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSemilocMaxIdeals.lean#L69-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSemilocMaxIdeals.lean#L69-L75

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocMaxIdeals
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFibreOverFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocIntegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsLocRingDimOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AvoidRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PSemilocMaxIdeals
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter
open GroundTheory.Heights₂.Heights.Inter.SemilocMaxIdeals
open regularityLocalFlat_holds
set_option linter.unusedSectionVars false
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  (P : Ideal (MRing ι)) [P.IsPrime] (𝒲 : Set (Ideal (MRing ι)))

theorem P2M_GroundTheory_Heights__Heights_Inter_SemilocMaxIdeals_frac_mem_c6800c83aff2 {u w : MRing ι} {a : K → ℕ} (hu : IsMultiHomog u a) (hw : IsMultiHomog w a) (hwP : w ∉ P)
    (hwW : ∀ W ∈ 𝒲, w ∉ W) : fracHom P u / fracHom P w ∈ semiLocRing P 𝒲 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«SemilocMaxIdeals».«frac_mem» := P2M_GroundTheory_Heights__Heights_Inter_SemilocMaxIdeals_frac_mem_c6800c83aff2
