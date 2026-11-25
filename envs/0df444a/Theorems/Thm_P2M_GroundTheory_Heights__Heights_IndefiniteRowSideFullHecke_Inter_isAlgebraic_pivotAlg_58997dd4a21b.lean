-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isAlgebraic_pivotAlg_58997dd4a21b
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isAlgebraic_pivotAlg_58997dd4a21b
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:22:38.403856+00:00
-- url     : https://prove2.me/theorems/3e201204-1a4f-400c-8bdd-02ab1b306ec1
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter is Algebraic pivot Alg 58997dd4a21b: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter is Algebraic pivo
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter is Algebraic pivot Alg 58997dd4a21b construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter is Algebraic pivot Alg 58997dd4a21b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFlagMinorsTrdeg.lean#L113-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFlagMinorsTrdeg.lean#L113-L130

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagMinorsTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagPivotIdentity
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagPivotAlgIndep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagMinorsTrdeg
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
open MvPolynomial
variable (F : Type) [Field F] (n : ℕ)

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isAlgebraic_pivotAlg_58997dd4a21b (h₁ : FlagPivotIdentity.Statement)
    (hne : ∀ a : Fin (n - 1), leadMinor (genMat F n) a ≠ 0) :
    Algebra.IsAlgebraic (pivotAlg F n) (flagMinorAlg F n) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«isAlgebraic_pivotAlg» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isAlgebraic_pivotAlg_58997dd4a21b
