-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_LinEmbed_isProjVarF_comap_418cc18913ce
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_LinEmbed_isProjVarF_comap_418cc18913ce
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:02:56.899347+00:00
-- url     : https://prove2.me/theorems/1ec1c64e-b445-4970-8229-6525d5e55e5b
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Lin Embed is Proj Var F comap 418cc18913ce: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Lin Embed
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Lin Embed is Proj Var F comap 418cc18913ce construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Lin Embed is Proj Var F comap 418cc18913ce property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/LinEmbedAlg.lean#L266-L271
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/LinEmbedAlg.lean#L266-L271

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LinEmbedSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CurvePt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemMinimalPrimesOfMemDivSuppDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpecialMultAt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LinEmbedAlg
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.LinEmbed
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
set_option linter.unusedSectionVars false
variable {F : Type} [Field F] {K K' : Type} [Fintype K] [Fintype K'] {ι : K → Type} {ι' : K' → Type}
  [∀ k, Fintype (ι k)] [∀ k', Fintype (ι' k')] {e : K' ≃ K} {A : ∀ k', ι' k' → ι (e k') → F}
variable (hA : ∀ k', Function.Injective (Matrix.of (A k')).mulVec)
include hA

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_LinEmbed_isProjVarF_comap_418cc18913ce {V : Ideal (MRingOver F ι)} {d : ℕ} (hV : IsProjVarF V d) :
    IsProjVarF (V.comap (blockLinSubst e A).toRingHom) d := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«LinEmbed».«isProjVarF_comap» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_LinEmbed_isProjVarF_comap_418cc18913ce
