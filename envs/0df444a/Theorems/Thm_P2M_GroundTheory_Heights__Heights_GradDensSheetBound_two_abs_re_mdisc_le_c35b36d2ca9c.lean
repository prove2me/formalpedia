-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GradDensSheetBound_two_abs_re_mdisc_le_c35b36d2ca9c
-- name    : P2M_GroundTheory_Heights__Heights_GradDensSheetBound_two_abs_re_mdisc_le_c35b36d2ca9c
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:18:13.314797+00:00
-- url     : https://prove2.me/theorems/12e2e2d2-2169-4c08-bec4-6230cbd85806
-- title:
--   P2 M Ground Theory Heights  Heights Grad Dens Sheet Bound two abs re mdisc le c35b36d2ca9c: P2 M Ground Theory Heights  Heights Grad Dens Sheet Bound two abs re mdisc le c35b36d2ca9c
-- statement:
--   The P2 M Ground Theory Heights  Heights Grad Dens Sheet Bound two abs re mdisc le c35b36d2ca9c construction uses the P2 M Ground Theory Heights  Heights Grad Dens Sheet Bound two abs re mdisc le c35b36d2ca9c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGradDensSheetBound.lean#L37-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGradDensSheetBound.lean#L37-L95

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCutOffBoundaryParts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGradDensSheetBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ComplexSets ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A Matrix
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.GradDensSheetBound

theorem P2M_GroundTheory_Heights__Heights_GradDensSheetBound_two_abs_re_mdisc_le_c35b36d2ca9c {n : ℕ} (x y : Fin (n + 1) → ℂ)
    (A W : Fin n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (c : ℝ) (hc : 0 < c)
    (hle : ∀ i, ((c : ℂ) • W i - A i).PosSemidef) (hge : ∀ i, (A i + (c : ℂ) • W i).PosSemidef) :
    2 * |(mdisc (Fin.cons (vecMulVec x (star y)) A :
        Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)).re| ≤
      3 ^ (n + 1) * c ^ n *
        ((mdisc (Fin.cons (vecMulVec x (star x)) W :
            Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)).re +
          (mdisc (Fin.cons (vecMulVec y (star y)) W :
            Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)).re) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GradDensSheetBound».«two_abs_re_mdisc_le» := P2M_GroundTheory_Heights__Heights_GradDensSheetBound_two_abs_re_mdisc_le_c35b36d2ca9c
