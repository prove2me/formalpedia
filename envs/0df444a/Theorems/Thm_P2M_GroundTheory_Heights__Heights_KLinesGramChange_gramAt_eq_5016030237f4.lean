-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesGramChange_gramAt_eq_5016030237f4
-- name    : P2M_GroundTheory_Heights__Heights_KLinesGramChange_gramAt_eq_5016030237f4
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:09:52.321053+00:00
-- url     : https://prove2.me/theorems/516fe2bb-ac8e-45a1-a356-addfbd2e0e62
-- title:
--   P2 M Ground Theory Heights  Heights KLines Gram Change gram At eq 5016030237f4: P2 M Ground Theory Heights  Heights KLines Gram Change gram At eq 5016030237f4
-- statement:
--   The P2 M Ground Theory Heights  Heights KLines Gram Change gram At eq 5016030237f4 construction uses the P2 M Ground Theory Heights  Heights KLines Gram Change gram At eq 5016030237f4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLinesGramChange.lean#L15-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLinesGramChange.lean#L15-L23

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesGramChange
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
open Matrix
open GroundTheory.Heights₂.Heights.KLinesGramChange

theorem P2M_GroundTheory_Heights__Heights_KLinesGramChange_gramAt_eq_5016030237f4 {K : Type*} [Field K] {n : ℕ} (h : Matrix (Fin n) (Fin n) ℂ) (σ : K →+* ℂ)
    {ι : Type*} [Fintype ι] (u : ι → Fin n → K) :
    gramAt h σ u = (colMatrix σ u)ᴴ * h * colMatrix σ u := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KLinesGramChange».«gramAt_eq» := P2M_GroundTheory_Heights__Heights_KLinesGramChange_gramAt_eq_5016030237f4
