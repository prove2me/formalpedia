-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_fiberRank_injective_on_fiber
-- name    : QEC.Coding.BDL26RandomPerturbation.fiberRank_injective_on_fiber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:51:27.233683+00:00
-- url     : https://prove2.me/theorems/646fd2ea-08ae-4c2b-808f-9ccbe8a20f47
-- title:
--   BDL26 Random Perturbation: fiber Rank injective on fiber
-- statement:
--   The BDL26 Random Perturbation construction uses the fiber Rank injective on fiber property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/Coloring.lean#L51-L58
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/Coloring.lean#L51-L58

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Incidence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Coloring
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26BoundedValence
variable {T A : Type*} [Fintype T] [DecidableEq T] [DecidableEq A]
variable (key : T → ℕ) (f : T → A)

theorem QEC.Coding.BDL26RandomPerturbation.fiberRank_injective_on_fiber (hkey : Function.Injective key)
    (a b : T) (hf : f a = f b) (hr : fiberRank key f a = fiberRank key f b) : a = b := by sorry
