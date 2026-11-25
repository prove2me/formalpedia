-- Prove2me | Theorems.Thm_P2M_Formalism_L2_FormalSeriesBounds_Cart_Good_c0__int_185a1ab43a5f
-- name    : P2M_Formalism_L2_FormalSeriesBounds_Cart_Good_c0__int_185a1ab43a5f
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:14:43.941848+00:00
-- url     : https://prove2.me/theorems/52c9445f-2f4c-40dc-9cee-f97088a54089
-- title:
--   P2 M Formalism L2 Formal Series Bounds Cart Good c0  int 185a1ab43a5f: P2 M Formalism L2 Formal Series Bounds Cart Good c0  int 185a1ab43a5f
-- statement:
--   The P2 M Formalism L2 Formal Series Bounds Cart Good c0  int 185a1ab43a5f construction uses the P2 M Formalism L2 Formal Series Bounds Cart Good c0  int 185a1ab43a5f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ScaledSecondIntegral.lean#L181-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ScaledSecondIntegral.lean#L181-L184

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

theorem P2M_Formalism_L2_FormalSeriesBounds_Cart_Good_c0__int_185a1ab43a5f {a : ZMod d} {u : I → C} {x : ℕ → I ⊕ J → C}
    (h : X.Good a u x) (j : J) : V.Ge 0 (X.c0' x j) := by sorry

alias «Formalism».«L2».«FormalSeriesBounds».«Cart».«Good».«c0'_int» := P2M_Formalism_L2_FormalSeriesBounds_Cart_Good_c0__int_185a1ab43a5f
