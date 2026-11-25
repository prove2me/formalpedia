-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesLineDegree_inter_line_12696afb69e9
-- name    : P2M_GroundTheory_Heights__Heights_KLinesLineDegree_inter_line_12696afb69e9
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:27:24.619265+00:00
-- url     : https://prove2.me/theorems/de5ed24c-d8d4-50a5-a650-1d40f6f4d7db
-- title:
--   P2 M Ground Theory Heights  Heights KLines Line Degree inter line 12696afb69e9: P2 M Ground Theory Heights  Heights KLines Line Degree inter line 12696afb69e9
-- statement:
--   The P2 M Ground Theory Heights  Heights KLines Line Degree inter line 12696afb69e9 construction uses the P2 M Ground Theory Heights  Heights KLines Line Degree inter line 12696afb69e9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLinesLineDegree.lean#L28-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLinesLineDegree.lean#L28-L50

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesLineDegree
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
open NumberField Matrix
open scoped nonZeroDivisors
noncomputable section
open GroundTheory.Heights₂.Heights.KLinesLineDegree
variable {K : Type} [Field K] {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_KLinesLineDegree_inter_line_12696afb69e9 (a : Fin n → FractionalIdeal (𝓞 K)⁰ K) (x : Fin n) :
    (idealLattice a ⊓ (Submodule.span K
        (Set.range fun _ : Fin 1 => (Pi.single x 1 : Fin n → K))).restrictScalars (𝓞 K)).toAddSubgroup =
      ((a x : Submodule (𝓞 K) K).toAddSubgroup).map (AddMonoidHom.single (fun _ : Fin n => K) x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KLinesLineDegree».«inter_line» := P2M_GroundTheory_Heights__Heights_KLinesLineDegree_inter_line_12696afb69e9
