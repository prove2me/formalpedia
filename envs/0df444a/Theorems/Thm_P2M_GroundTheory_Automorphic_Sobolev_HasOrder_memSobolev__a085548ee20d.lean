-- Prove2me | Theorems.Thm_P2M_GroundTheory_Automorphic_Sobolev_HasOrder_memSobolev__a085548ee20d
-- name    : P2M_GroundTheory_Automorphic_Sobolev_HasOrder_memSobolev__a085548ee20d
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T02:01:54.350443+00:00
-- url     : https://prove2.me/theorems/09db72df-1ff5-4646-9e13-2240e2d31ebb
-- title:
--   P2 M Ground Theory Automorphic Sobolev Has Order mem Sobolev  a085548ee20d: P2 M Ground Theory Automorphic Sobolev Has Order mem Sobolev  a085548ee20d
-- statement:
--   The P2 M Ground Theory Automorphic Sobolev Has Order mem Sobolev  a085548ee20d construction uses the P2 M Ground Theory Automorphic Sobolev Has Order mem Sobolev  a085548ee20d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticOperators.lean#L29-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticOperators.lean#L29-L31

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMultiplication
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.Sobolev
open TemperedDistribution MeasureTheory FourierTransform LineDeriv
open scoped SchwartzMap ENNReal ContDiff
noncomputable section
set_option linter.unusedSectionVars false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
open GroundTheory.Automorphic.Sobolev.HasOrder
variable {T T₁ T₂ : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)} {k k₁ k₂ : ℝ}

theorem P2M_GroundTheory_Automorphic_Sobolev_HasOrder_memSobolev__a085548ee20d (h : HasOrder T k) {s t : ℝ} (hst : t = s - k) {u : 𝓢'(E, ℂ)}
    (hu : MemSobolev s 2 u) : MemSobolev t 2 (T u) := by sorry

alias «GroundTheory».«Automorphic».«Sobolev».«HasOrder».«memSobolev'» := P2M_GroundTheory_Automorphic_Sobolev_HasOrder_memSobolev__a085548ee20d
