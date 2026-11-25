-- Prove2me | Theorems.Thm_P2M_GroundTheory_ProfCoh_AdditiveFunction_g_eq_of_finite_cokernel__fa6a384fcd8d
-- name    : P2M_GroundTheory_ProfCoh_AdditiveFunction_g_eq_of_finite_cokernel__fa6a384fcd8d
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:55:24.17427+00:00
-- url     : https://prove2.me/theorems/6d594b30-10bd-4abc-9d6d-189752c71576
-- title:
--   P2 M Ground Theory Prof Coh Additive Function g eq of finite cokernel  fa6a384fcd8d: P2 M Ground Theory Prof Coh Additive Function g eq of finite cokernel  fa6a384fcd8d
-- statement:
--   The P2 M Ground Theory Prof Coh Additive Function g eq of finite cokernel  fa6a384fcd8d construction uses the P2 M Ground Theory Prof Coh Additive Function g eq of finite cokernel  fa6a384fcd8d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/Additive.lean#L129-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/Additive.lean#L129-L140

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_AdditiveSnake
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_Additive
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
universe u v
open Representation
open GroundTheory.ProfCoh.AdditiveFunction
variable {l : ℕ} {Γ : Type v} [Group Γ] (d : AdditiveFunction.{u} l Γ)

theorem P2M_GroundTheory_ProfCoh_AdditiveFunction_g_eq_of_finite_cokernel__fa6a384fcd8d {A B : Type u} [AddCommGroup A] [AddCommGroup B]
    [DistribMulAction Γ A] [DistribMulAction Γ B] (f : B →+ A)
    (hfγ : ∀ (γ : Γ) (b : B), f (γ • b) = γ • f b) (hf : Function.Injective f)
    [Finite (A ⧸ f.range)] [Finite (ModN A l)] [Finite (TorsN A l)] : d.g A = d.g B := by sorry

alias «GroundTheory».«ProfCoh».«AdditiveFunction».«g_eq_of_finite_cokernel'» := P2M_GroundTheory_ProfCoh_AdditiveFunction_g_eq_of_finite_cokernel__fa6a384fcd8d
