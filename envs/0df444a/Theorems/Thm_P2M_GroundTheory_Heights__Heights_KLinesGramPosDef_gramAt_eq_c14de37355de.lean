-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesGramPosDef_gramAt_eq_c14de37355de
-- name    : P2M_GroundTheory_Heights__Heights_KLinesGramPosDef_gramAt_eq_c14de37355de
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:09:54.283525+00:00
-- url     : https://prove2.me/theorems/b36417bd-9df3-4015-b513-ce4a3e0b6cba
-- title:
--   P2 M Ground Theory Heights  Heights KLines Gram Pos Def gram At eq c14de37355de: P2 M Ground Theory Heights  Heights KLines Gram Pos Def gram At eq c14de37355de
-- statement:
--   The P2 M Ground Theory Heights  Heights KLines Gram Pos Def gram At eq c14de37355de construction uses the P2 M Ground Theory Heights  Heights KLines Gram Pos Def gram At eq c14de37355de property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLinesGramPosDef.lean#L13-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLinesGramPosDef.lean#L13-L19

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesGramPosDef
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
open GroundTheory.Heights₂.Heights.KLinesGramPosDef
open Matrix
variable {K : Type*} [Field K] {n : ℕ} {ι : Type*}

theorem P2M_GroundTheory_Heights__Heights_KLinesGramPosDef_gramAt_eq_c14de37355de (h : Matrix (Fin n) (Fin n) ℂ) (σ : K →+* ℂ) (u : ι → Fin n → K) :
    gramAt h σ u = (((Matrix.of fun j a => u a j).map σ)ᴴ * h *
      (Matrix.of fun j a => u a j).map σ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KLinesGramPosDef».«gramAt_eq» := P2M_GroundTheory_Heights__Heights_KLinesGramPosDef_gramAt_eq_c14de37355de
