-- Prove2me | Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_PrefixProjection_stream_suffix_injective
-- name    : QEC.Coding.BitTuring.UnaryArithmetic.PrefixProjection.stream_suffix_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:08:57.373848+00:00
-- url     : https://prove2.me/theorems/57957c5b-1a40-445c-ae23-d7fb352c73be
-- title:
--   Prefix Projection: stream suffix injective
-- statement:
--   Actual finite instructions or proved configuration, execution, budget, faithful encoding or source certificate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryPrefixProjection.lean#L218-L233
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryPrefixProjection.lean#L218-L233

import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Definitions.Def_QEC_Coding_BitTuring_UnaryPrefixProjection
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.PrefixProjection
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic
open Turing StateTransition FieldProjection
variable (n:ℕ) (keep:Fin (n+1)→Bool)
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
variable (n:ℕ) (keep:Fin (n+1)→Bool)

theorem QEC.Coding.BitTuring.UnaryArithmetic.PrefixProjection.stream_suffix_injective (xs ys:List ℕ) (s t:List Bool) (hl:xs.length=ys.length)
    (h:stream xs++s=stream ys++t):xs=ys ∧ s=t := by sorry
