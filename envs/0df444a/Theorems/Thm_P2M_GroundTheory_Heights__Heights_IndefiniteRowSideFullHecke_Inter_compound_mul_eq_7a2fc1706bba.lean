-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_compound_mul_eq_7a2fc1706bba
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_compound_mul_eq_7a2fc1706bba
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:22:04.466806+00:00
-- url     : https://prove2.me/theorems/d1a29b2f-ad22-4ace-a659-d892b745f663
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter compound mul eq 7a2fc1706bba: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter compound mul eq 7a2fc170
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter compound mul eq 7a2fc1706bba construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter compound mul eq 7a2fc1706bba property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFlagFibre.lean#L100-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFlagFibre.lean#L100-L108

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_compound_mul_eq_7a2fc1706bba {m : ℕ} (B : Matrix (Fin n) (Fin N1) F) (C : Matrix (Fin N1) (Fin n) F) (hBC : B * C = 1)
    (S' S'' : {S : Finset (Fin n) // S.card = m}) :
    ∑ S : {S : Finset (Fin N1) // S.card = m},
        (C.submatrix (S.1.orderEmbOfFin S.2) (S''.1.orderEmbOfFin S''.2)).det *
          (B.submatrix (S'.1.orderEmbOfFin S'.2) (S.1.orderEmbOfFin S.2)).det =
      if S' = S'' then 1 else 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«compound_mul_eq» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_compound_mul_eq_7a2fc1706bba
