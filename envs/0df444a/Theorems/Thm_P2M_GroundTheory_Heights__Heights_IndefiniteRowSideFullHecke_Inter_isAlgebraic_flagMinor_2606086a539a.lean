-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isAlgebraic_flagMinor_2606086a539a
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isAlgebraic_flagMinor_2606086a539a
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:31:54.333882+00:00
-- url     : https://prove2.me/theorems/7b06ca9b-b72c-48c8-bd07-248ef451cfa2
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter is Algebraic flag Minor 2606086a539a: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter is Algebraic fla
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter is Algebraic flag Minor 2606086a539a construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter is Algebraic flag Minor 2606086a539a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFlagMinorsTrdeg.lean#L91-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFlagMinorsTrdeg.lean#L91-L111

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isAlgebraic_flagMinor_2606086a539a (h₁ : FlagPivotIdentity.Statement)
    (hne : ∀ a : Fin (n - 1), leadMinor (genMat F n) a ≠ 0) (q : Σ j, PluckerBlocks n n j) :
    IsAlgebraic (pivotAlg F n)
      (⟨flagMinor (genMat F n) q.1 q.2, Algebra.subset_adjoin ⟨q, rfl⟩⟩ : flagMinorAlg F n) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«isAlgebraic_flagMinor» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isAlgebraic_flagMinor_2606086a539a
