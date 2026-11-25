-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_SemilocResidueAdjoin_isMultiHomogIdeal_map_ef06bc88f37f
-- name    : P2M_GroundTheory_Heights__Heights_Inter_SemilocResidueAdjoin_isMultiHomogIdeal_map_ef06bc88f37f
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:46:14.805705+00:00
-- url     : https://prove2.me/theorems/4c3131d2-e971-48fb-bed3-41fdee621224
-- title:
--   P2 M Ground Theory Heights  Heights Inter Semiloc Residue Adjoin is Multi Homog Ideal map ef06bc88f37f: P2 M Ground Theory Heights  Heights Inter Semiloc Residue Adjoin is Multi Homog Ideal map ef06bc
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Semiloc Residue Adjoin is Multi Homog Ideal map ef06bc88f37f construction uses the P2 M Ground Theory Heights  Heights Inter Semiloc Residue Adjoin is Multi Homog Ideal map ef06bc88f37f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSemilocResidueAdjoin.lean#L12-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSemilocResidueAdjoin.lean#L12-L19

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StSemilocResidueFrac
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PSemilocRankAdjoin
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PSemilocResidueAdjoin
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_SemilocRankAdjoin_isMultiHomogIdeal_map_81a0ea2d0932

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem P2M_GroundTheory_Heights__Heights_Inter_SemilocResidueAdjoin_isMultiHomogIdeal_map_ef06bc88f37f {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {R : Type} [CommRing R] (φ : ℤ →+* R) {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P) :
    IsMultiHomogIdeal (P.map (MvPolynomial.map φ : MRing ι →+* MRingOver R ι)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«SemilocResidueAdjoin».«isMultiHomogIdeal_map» := P2M_GroundTheory_Heights__Heights_Inter_SemilocResidueAdjoin_isMultiHomogIdeal_map_ef06bc88f37f
