-- Prove2me | Theorems.Thm_PositivityTheory_RgUd_TP_Nil_Asm_bez2
-- name    : PositivityTheory.RgUd.TP.Nil.Asm.bez2
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:03:32.189717+00:00
-- url     : https://prove2.me/theorems/e08d79b1-5cfb-5c73-83f4-0cbdd829ab57
-- title:
--   Asm: bez2
-- statement:
--   The Asm construction uses the bez2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/TwistedPieces/IntegralParts/BezoutHypotheses/Bez2.lean#L9-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/TwistedPieces/IntegralParts/BezoutHypotheses/Bez2.lean#L9-L46

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_NilpotentHypotheses_AevalProdLinearFactors
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_IntegralParts_BezoutHypotheses_Bez2
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial PositivityTheory.RgUd.T.Nil.Asm
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Nil PositivityTheory.RgUd.TP.Nil.Asm

theorem PositivityTheory.RgUd.TP.Nil.Asm.bez2 {M : Type*} [AddCommGroup M] [Module ℂ M] (K : Submodule ℂ M) (R R' : M →ₗ[ℂ] M)
    (hRR : R ∘ₗ R' = LinearMap.id) (hR'R : R' ∘ₗ R = LinearMap.id) (hK : ∀ m ∈ K, R m ∈ K) (c : ℝ) (hc : 1 < c)
    (d : ℝ) (a b : List ℝ) (hab : ∀ x ∈ a, ∀ y ∈ b, y + x ≠ d) (ζ : M)
    (h1 : ((b.map fun y => R - ((c ^ y : ℝ) : ℂ) • LinearMap.id).prod : Module.End ℂ M) ζ ∈ K)
    (h2 : ((a.map fun x => ((c ^ d : ℝ) : ℂ) • R' - ((c ^ x : ℝ) : ℂ) • LinearMap.id).prod : Module.End ℂ M) ζ ∈ K) :
    ζ ∈ K := by sorry
