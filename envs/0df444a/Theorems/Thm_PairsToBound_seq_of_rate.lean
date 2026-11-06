-- Prove2me | Theorems.Thm_PairsToBound_seq_of_rate
-- name    : PairsToBound.seq_of_rate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:53:00.687138+00:00
-- url     : https://prove2.me/theorems/bd591dae-9274-41b0-8808-52d4fc344089
-- title:
--   Pairs To Bound: seq of rate
-- statement:
--   Parts (a) and (b) of Theorem A as a sequence of levels, with the constant before the pieces,
--   from the statements `StChain2`, `StRate2`, `StSolveG2` and `StNeedG` taken as hypotheses. For every
--   c there is a C₀ such that for all programs P with parameters (ρ, c) and P.m = 1, 1/2 ≤ ρ < 1, every
--   x₀ ≥ 18 with 2^x₀ ≥ c + 5 and every program `pick` that finds the level, the solver made of P has a
--   sequence of levels for the numbers e_ℓ of display (40) with the
--   constant C₀, whose ℓ-th index is the schedule of display (40) and whose level is picked by `pick`.
--   The proof is that of `GeneralPieces.seq_of_pick`; C₀ = C + 10 for the C of part (b).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/PairsToBound/Pairs.lean#L54-L108
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/PairsToBound/Pairs.lean#L54-L108

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PairsToBound_Defs
import Definitions.Def_GeneralPieces_Rec_Seq
import Definitions.Def_GeneralPieces_ThmRunningTime
import Definitions.Def_GeneralPieces_Rec_Chain
import Definitions.Def_GeneralPieces_Rec_Rate
import Definitions.Def_GeneralPieces_Rec_PartB
import Definitions.Def_GeneralPieces_Num_PartA
import Definitions.Def_GeneralPieces_Num_PartAUse
import Definitions.Def_GeneralPieces_Num_Asymptotic
import Definitions.Def_ClauseBound_Alg_Need
import Definitions.Def_PairsToBound_Pairs
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open PairsToBound
open Turing Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Gen ClauseBound.Gen.Seq Levels.Gen GeneralPieces MainTheoremForms

theorem PairsToBound.seq_of_rate (hCh : StChain2) (hR : StRate2) (hSolve : ∀ P, StSolveG2 P) (hNeed : ∀ P, StNeedG P) (c : ℕ) :
    ∃ C₀ : ℕ, ∀ (P : PiecesF) (ρ : ℝ) (x₀ : ℕ), 1 / 2 ≤ ρ → ρ < 1 → Par P ρ c → P.m = 1 → 18 ≤ x₀ → c + 5 ≤ 2 ^ x₀ →
      ∀ pick : U → U × (List Step × U), PolyT pick → (∀ b, (pick b).2 = idx P x₀ (pick b).1.length) → (∀ b, K x₀ 0 ≤ b.length → K x₀ (pick b).1.length ≤ b.length) →
        (∀ b, b.length < K x₀ ((pick b).1.length + 1)) →
        ∃ Q : (solverOf P).Seq (e ρ x₀) C₀, (∀ l, Q.idx l = idx P x₀ l) ∧ Q.pick = pick := by sorry
