-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_fibreDeg_flag_5a65a79bb332
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_fibreDeg_flag_5a65a79bb332
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:23:43.340478+00:00
-- url     : https://prove2.me/theorems/654c55ff-ed57-5dd4-b077-b6a8f4dbdb11
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter fibre Deg flag 5a65a79bb332: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter fibre Deg flag 5a65a79bb3
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter fibre Deg flag 5a65a79bb332 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter fibre Deg flag 5a65a79bb332 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFlagFibre.lean#L38-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFlagFibre.lean#L38-L43

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_fibreDeg_flag_5a65a79bb332 (a : K ⊕ Fin (n - 1) → ℤ) :
    fibreDeg Sum.inl a = (fun j => a (Sum.inr j)) ∘ (flagFibreBlocksEquiv (K := K) (n := n)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«fibreDeg_flag» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_fibreDeg_flag_5a65a79bb332
