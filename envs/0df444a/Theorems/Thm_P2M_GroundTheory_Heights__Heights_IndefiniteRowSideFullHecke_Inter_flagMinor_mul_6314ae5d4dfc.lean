-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_flagMinor_mul_6314ae5d4dfc
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_flagMinor_mul_6314ae5d4dfc
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:31:19.348153+00:00
-- url     : https://prove2.me/theorems/7b2eeee6-d34d-402c-870b-00d3c6b0ee5d
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter flag Minor mul 6314ae5d4dfc: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter flag Minor mul 6314ae5d4d
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter flag Minor mul 6314ae5d4dfc construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter flag Minor mul 6314ae5d4dfc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFlagFibre.lean#L45-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFlagFibre.lean#L45-L51

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
variable {K : Type} {ι : K → Type} {N1 n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_flagMinor_mul_6314ae5d4dfc {R : Type} [CommRing R] (M : Matrix (Fin n) (Fin n) R) (B' : Matrix (Fin n) (Fin N1) R)
    (j : Fin (n - 1)) (S : PluckerBlocks N1 n j) :
    flagMinor (M * B') j S = ∑ S' : PluckerBlocks n n j,
      flagMinor M j S' * (B'.submatrix (S'.1.orderEmbOfFin S'.2) (S.1.orderEmbOfFin S.2)).det := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«flagMinor_mul» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_flagMinor_mul_6314ae5d4dfc
