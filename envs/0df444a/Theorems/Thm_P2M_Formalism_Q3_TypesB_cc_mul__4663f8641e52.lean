-- Prove2me | Theorems.Thm_P2M_Formalism_Q3_TypesB_cc_mul__4663f8641e52
-- name    : P2M_Formalism_Q3_TypesB_cc_mul__4663f8641e52
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:07:15.001349+00:00
-- url     : https://prove2.me/theorems/45effdb1-dada-441b-9bb7-39a1012cab1f
-- title:
--   P2 M Formalism Q3 Types B cc mul  4663f8641e52: P2 M Formalism Q3 Types B cc mul  4663f8641e52
-- statement:
--   The P2 M Formalism Q3 Types B cc mul  4663f8641e52 construction uses the P2 M Formalism Q3 Types B cc mul  4663f8641e52 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CMTypeGalois/CMTypeFrobenius/TypesB.lean#L12-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CMTypeGalois/CMTypeFrobenius/TypesB.lean#L12-L13

import Mathlib
import Definitions.Def_Formalism_CMTypeGalois_StatementGroup
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_TypesB
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
open Formalism.Q3.TypesB
variable {G : Type*} [CommGroup G] [DecidableEq G] {c : G}

theorem P2M_Formalism_Q3_TypesB_cc_mul__4663f8641e52 (hc : c * c = 1) (g : G) : c * (c * g) = g := by sorry

alias «Formalism».«Q3».«TypesB».«cc_mul'» := P2M_Formalism_Q3_TypesB_cc_mul__4663f8641e52
