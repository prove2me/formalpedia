-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_det_one_submatrix_6335cc6abd88
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_det_one_submatrix_6335cc6abd88
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:22:47.004516+00:00
-- url     : https://prove2.me/theorems/c4a7984d-8af2-4118-96bc-65505299a21a
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter det one submatrix 6335cc6abd88: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter det one submatrix 6335
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter det one submatrix 6335cc6abd88 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter det one submatrix 6335cc6abd88 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFlagFibre.lean#L82-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFlagFibre.lean#L82-L98

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FlagBundleSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LinEmbedSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FlagDimSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_RelBaseChangeSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCauchyBinet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsUniqueStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_InhDivCycleOfSuppEmpty
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagFibre
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
variable {F : Type} [Field F] {N1 n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_det_one_submatrix_6335cc6abd88 {m : ℕ} (S' S'' : {S : Finset (Fin n) // S.card = m}) :
    ((1 : Matrix (Fin n) (Fin n) F).submatrix (S'.1.orderEmbOfFin S'.2) (S''.1.orderEmbOfFin S''.2)).det =
      if S' = S'' then 1 else 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«det_one_submatrix» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_det_one_submatrix_6335cc6abd88
