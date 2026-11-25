-- Prove2me | Theorems.Thm_P2M_Formalism_Q3_mul_ne_one_iff__67a0a7119a81
-- name    : P2M_Formalism_Q3_mul_ne_one_iff__67a0a7119a81
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:01:01.689714+00:00
-- url     : https://prove2.me/theorems/d3106216-594a-4d54-9385-985258666bd0
-- title:
--   P2 M Formalism Q3 mul ne one iff  67a0a7119a81: P2 M Formalism Q3 mul ne one iff  67a0a7119a81
-- statement:
--   The P2 M Formalism Q3 mul ne one iff  67a0a7119a81 construction uses the P2 M Formalism Q3 mul ne one iff  67a0a7119a81 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CMTypeGalois/CMTypeFrobenius/TypesA.lean#L29-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CMTypeGalois/CMTypeFrobenius/TypesA.lean#L29-L37

import Mathlib
import Definitions.Def_Formalism_CMTypeGalois_StatementGroup
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_TypesA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.Q3
variable {G : Type*} [CommGroup G] [DecidableEq G] {c : G}

theorem P2M_Formalism_Q3_mul_ne_one_iff__67a0a7119a81 (hc : c * c = 1) (g : G) : c * g ≠ 1 ↔ g ≠ c := by sorry

alias «Formalism».«Q3».«mul_ne_one_iff'» := P2M_Formalism_Q3_mul_ne_one_iff__67a0a7119a81
