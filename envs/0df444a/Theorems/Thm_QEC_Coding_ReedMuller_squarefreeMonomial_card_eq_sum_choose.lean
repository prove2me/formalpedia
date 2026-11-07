-- Prove2me | Theorems.Thm_QEC_Coding_ReedMuller_squarefreeMonomial_card_eq_sum_choose
-- name    : QEC.Coding.ReedMuller.squarefreeMonomial_card_eq_sum_choose
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:57:04.055248+00:00
-- url     : https://prove2.me/theorems/17d71ef2-5b4c-46b0-a903-c26955ec9c8e
-- title:
--   Reed Muller: squarefree Monomial card eq sum choose
-- statement:
--   The number of squarefree monomials through degree `r` is the exact
--   cumulative binomial sum.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ReedMuller/Base.lean#L199-L202
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ReedMuller/Base.lean#L199-L202

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Coding_ReedMuller_Base
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.ReedMuller
open scoped BigOperators

theorem QEC.Coding.ReedMuller.squarefreeMonomial_card_eq_sum_choose (m r : Nat) :
    Fintype.card (SquarefreeMonomial m r) =
      ∑ i ∈ Finset.Icc 0 r, Nat.choose m i := by sorry
