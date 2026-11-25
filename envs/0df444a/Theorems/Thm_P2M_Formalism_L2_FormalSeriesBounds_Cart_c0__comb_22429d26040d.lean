-- Prove2me | Theorems.Thm_P2M_Formalism_L2_FormalSeriesBounds_Cart_c0__comb_22429d26040d
-- name    : P2M_Formalism_L2_FormalSeriesBounds_Cart_c0__comb_22429d26040d
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:14:37.040983+00:00
-- url     : https://prove2.me/theorems/577312a8-9f78-49ed-9536-bf2c08f8578d
-- title:
--   P2 M Formalism L2 Formal Series Bounds Cart c0  comb 22429d26040d: P2 M Formalism L2 Formal Series Bounds Cart c0  comb 22429d26040d
-- statement:
--   The P2 M Formalism L2 Formal Series Bounds Cart c0  comb 22429d26040d construction uses the P2 M Formalism L2 Formal Series Bounds Cart c0  comb 22429d26040d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ScaledSecondIntegral.lean#L209-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ScaledSecondIntegral.lean#L209-L212

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GeNatCast
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ScaledSecondIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Finset
noncomputable section
variable {C : Type*} [Field C] {V : VF C} {d : ℕ} {I J : Type*}
open Formalism.L2.FormalSeriesBounds.Cart
variable (X : Cart V d I J)
variable {X}

theorem P2M_Formalism_L2_FormalSeriesBounds_Cart_c0__comb_22429d26040d {ι : Type*} (s : Finset ι) (x : ι → ℕ → I ⊕ J → C) (co : ι → C) (j : J) :
    X.c0' (∑ k ∈ s, teich V.l (co k) (x k)) j = ∑ k ∈ s, co k ^ V.l * X.c0' (x k) j := by sorry

alias «Formalism».«L2».«FormalSeriesBounds».«Cart».«c0'_comb» := P2M_Formalism_L2_FormalSeriesBounds_Cart_c0__comb_22429d26040d
