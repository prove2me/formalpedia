-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_mem_span_sup_sq_of_polyDiff_mem_39a5af881036
-- name    : P2M_GroundTheory_Heights__Heights_mem_span_sup_sq_of_polyDiff_mem_39a5af881036
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:49:04.787805+00:00
-- url     : https://prove2.me/theorems/d128162b-86b8-479f-a916-6a14fb155f1a
-- title:
--   P2 M Ground Theory Heights  Heights mem span sup sq of poly Diff mem 39a5af881036: P2 M Ground Theory Heights  Heights mem span sup sq of poly Diff mem 39a5af881036
-- statement:
--   The P2 M Ground Theory Heights  Heights mem span sup sq of poly Diff mem 39a5af881036 construction uses the P2 M Ground Theory Heights  Heights mem span sup sq of poly Diff mem 39a5af881036 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PPolyLocalGeneratorsDiff.lean#L116-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PPolyLocalGeneratorsDiff.lean#L116-L131

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsPolyLocalGenerators
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PPolyLocalGeneratorsDiff
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
open MvPolynomial Module
noncomputable section
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_mem_span_sup_sq_of_polyDiff_mem_39a5af881036 (p : Fin n → ℂ) {ι : Type*} [Fintype ι]
    (h : ι → MvPolynomial (Fin n) ℂ) (hh : ∀ i, eval p (h i) = 0) {f : MvPolynomial (Fin n) ℂ}
    (hf : eval p f = 0) (hd : polyDiff p f ∈ Submodule.span ℂ (Set.range (polyDiff p ∘ h))) :
    f ∈ Ideal.span (Set.range h) ⊔ RingHom.ker (eval p) ^ 2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«mem_span_sup_sq_of_polyDiff_mem» := P2M_GroundTheory_Heights__Heights_mem_span_sup_sq_of_polyDiff_mem_39a5af881036
