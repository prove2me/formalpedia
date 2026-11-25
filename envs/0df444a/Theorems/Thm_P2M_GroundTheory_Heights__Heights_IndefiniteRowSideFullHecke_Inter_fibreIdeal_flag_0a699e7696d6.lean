-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_fibreIdeal_flag_0a699e7696d6
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_fibreIdeal_flag_0a699e7696d6
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:23:50.351188+00:00
-- url     : https://prove2.me/theorems/bef49f33-45da-5a8f-8020-1135721085b0
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter fibre Ideal flag 0a699e7696d6: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter fibre Ideal flag 0a699e
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter fibre Ideal flag 0a699e7696d6 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter fibre Ideal flag 0a699e7696d6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFlagFibre.lean#L143-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFlagFibre.lean#L143-L184

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
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {N1 n : ℕ}
omit [Fintype K] [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_fibreIdeal_flag_0a699e7696d6 (P : Ideal (MRing ι)) [hP : P.IsPrime] (B : Matrix (Fin n) (Fin N1) (FnField P)) :
    fibreIdeal Sum.inl (flagGenFibre P hP B) =
      (flagIdealOver (FnField P) n).comap
        (blockLinSubst (flagFibreBlocksEquiv (K := K)) (flagCompound (ι := ι) B)).toRingHom := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«fibreIdeal_flag» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_fibreIdeal_flag_0a699e7696d6
