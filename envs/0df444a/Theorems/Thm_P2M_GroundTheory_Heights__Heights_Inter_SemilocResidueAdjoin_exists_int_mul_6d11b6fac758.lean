-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_SemilocResidueAdjoin_exists_int_mul_6d11b6fac758
-- name    : P2M_GroundTheory_Heights__Heights_Inter_SemilocResidueAdjoin_exists_int_mul_6d11b6fac758
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:47:04.493836+00:00
-- url     : https://prove2.me/theorems/869e641b-7ce0-458e-85b5-0da97a129cf6
-- title:
--   P2 M Ground Theory Heights  Heights Inter Semiloc Residue Adjoin exists int mul 6d11b6fac758: P2 M Ground Theory Heights  Heights Inter Semiloc Residue Adjoin exists int mul 6d11b6fac758
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Semiloc Residue Adjoin exists int mul 6d11b6fac758 construction uses the P2 M Ground Theory Heights  Heights Inter Semiloc Residue Adjoin exists int mul 6d11b6fac758 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSemilocResidueAdjoin.lean#L21-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSemilocResidueAdjoin.lean#L21-L39

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

theorem P2M_GroundTheory_Heights__Heights_Inter_SemilocResidueAdjoin_exists_int_mul_6d11b6fac758 {σ F : Type} [Field F]
    (hF : ∀ c : F, ∃ a b : ℤ, (b : F) ≠ 0 ∧ c = a / b) (f : MvPolynomial σ F) :
    ∃ (g : MvPolynomial σ ℤ) (d : ℤ), (d : F) ≠ 0 ∧ C (d : F) * f = MvPolynomial.map (Int.castRingHom F) g := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«SemilocResidueAdjoin».«exists_int_mul» := P2M_GroundTheory_Heights__Heights_Inter_SemilocResidueAdjoin_exists_int_mul_6d11b6fac758
