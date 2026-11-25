-- Prove2me | Theorems.Thm_P2M_Formalism_WeaklyAdmissibleFiltrations_exwaF___70203564a2ca
-- name    : P2M_Formalism_WeaklyAdmissibleFiltrations_exwaF___70203564a2ca
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:02:00.765294+00:00
-- url     : https://prove2.me/theorems/02021010-200d-40fb-9c7a-a5ac452d9972
-- title:
--   P2 M Formalism Weakly Admissible Filtrations exwa F   70203564a2ca: P2 M Formalism Weakly Admissible Filtrations exwa F   70203564a2ca
-- statement:
--   The P2 M Formalism Weakly Admissible Filtrations exwa F   70203564a2ca construction uses the P2 M Formalism Weakly Admissible Filtrations exwa F   70203564a2ca property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WeaklyAdmissibleFiltrations/CrystallineStableLifts/ExwaFiltrationNegOneEqSpanSingle.lean#L68-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WeaklyAdmissibleFiltrations/CrystallineStableLifts/ExwaFiltrationNegOneEqSpanSingle.lean#L68-L68

import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CocyclesFunctorial
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CrystallineStableLifts_ExwaFiltrationNegOneEqSpanSingle
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.WeaklyAdmissibleFiltrations
open Module
variable {LL : Type} [Field LL] {n : ℕ} [NeZero n]

theorem P2M_Formalism_WeaklyAdmissibleFiltrations_exwaF___70203564a2ca (c : LL) (hc : c ≠ 0) (x : ZMod n → LL) : (exwaF c hc).φ x = exwaPhi c hc x := by sorry

alias «Formalism».«WeaklyAdmissibleFiltrations».«exwaF_φ» := P2M_Formalism_WeaklyAdmissibleFiltrations_exwaF___70203564a2ca
