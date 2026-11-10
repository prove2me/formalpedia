-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_fiberRank_strictMono
-- name    : QEC.Coding.BDL26RandomPerturbation.fiberRank_strictMono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:51:00.724835+00:00
-- url     : https://prove2.me/theorems/5035df71-e12e-426f-bd04-7da0d3ced351
-- title:
--   BDL26 Random Perturbation: fiber Rank strict Mono
-- statement:
--   The BDL26 Random Perturbation construction uses the fiber Rank strict Mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/Coloring.lean#L38-L49
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/Coloring.lean#L38-L49

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Incidence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Coloring
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26BoundedValence
variable {T A : Type*} [Fintype T] [DecidableEq T] [DecidableEq A]
variable (key : T → ℕ) (f : T → A)

theorem QEC.Coding.BDL26RandomPerturbation.fiberRank_strictMono (a b : T) (hf : f a = f b) (hk : key a < key b) :
    fiberRank key f a < fiberRank key f b := by sorry
