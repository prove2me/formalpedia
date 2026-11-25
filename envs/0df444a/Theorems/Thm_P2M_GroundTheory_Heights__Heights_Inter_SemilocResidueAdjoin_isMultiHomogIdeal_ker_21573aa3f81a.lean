-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_SemilocResidueAdjoin_isMultiHomogIdeal_ker_21573aa3f81a
-- name    : P2M_GroundTheory_Heights__Heights_Inter_SemilocResidueAdjoin_isMultiHomogIdeal_ker_21573aa3f81a
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:47:11.2138+00:00
-- url     : https://prove2.me/theorems/5be474a5-9b3c-4a00-b8e5-d3f86a00532c
-- title:
--   P2 M Ground Theory Heights  Heights Inter Semiloc Residue Adjoin is Multi Homog Ideal ker 21573aa3f81a: P2 M Ground Theory Heights  Heights Inter Semiloc Residue Adjoin is Multi Homog Ideal ker 21573a
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Semiloc Residue Adjoin is Multi Homog Ideal ker 21573aa3f81a construction uses the P2 M Ground Theory Heights  Heights Inter Semiloc Residue Adjoin is Multi Homog Ideal ker 21573aa3f81a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSemilocResidueAdjoin.lean#L41-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSemilocResidueAdjoin.lean#L41-L60

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StSemilocResidueFrac
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PSemilocRankAdjoin
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PSemilocResidueAdjoin
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

theorem P2M_GroundTheory_Heights__Heights_Inter_SemilocResidueAdjoin_isMultiHomogIdeal_ker_21573aa3f81a {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (hF : ∀ c : F, ∃ a b : ℤ, (b : F) ≠ 0 ∧ c = a / b)
    (x : (Σ k, ι k) → Ω) (hmh : IsMultiHomogIdeal (RingHom.ker (aeval x : MRing ι →ₐ[ℤ] Ω))) :
    IsMultiHomogIdeal (RingHom.ker (aeval x : MRingOver F ι →ₐ[F] Ω)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«SemilocResidueAdjoin».«isMultiHomogIdeal_ker» := P2M_GroundTheory_Heights__Heights_Inter_SemilocResidueAdjoin_isMultiHomogIdeal_ker_21573aa3f81a
