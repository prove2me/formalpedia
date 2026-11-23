-- Prove2me | Theorems.Thm_P2M_GlobalTheory_OrbitGrowth_mul_apply__1ef562d11778
-- name    : P2M_GlobalTheory_OrbitGrowth_mul_apply__1ef562d11778
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:03:00.814717+00:00
-- url     : https://prove2.me/theorems/7c7f030d-ef7b-4131-b482-7c2f58f39210
-- title:
--   P2 M Global Theory Orbit Growth mul apply  1ef562d11778: P2 M Global Theory Orbit Growth mul apply  1ef562d11778
-- statement:
--   The P2 M Global Theory Orbit Growth mul apply  1ef562d11778 construction uses the P2 M Global Theory Orbit Growth mul apply  1ef562d11778 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/MulApply.lean#L21-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/MulApply.lean#L21-L21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_MulApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.OrbitGrowth
variable {M : Type} [AddCommGroup M] [Module ℂ M]

theorem P2M_GlobalTheory_OrbitGrowth_mul_apply__1ef562d11778 (a b : Module.End ℂ M) (y : M) : (a * b) y = a (b y) := by sorry

alias «GlobalTheory».«OrbitGrowth».«mul_apply'» := P2M_GlobalTheory_OrbitGrowth_mul_apply__1ef562d11778
