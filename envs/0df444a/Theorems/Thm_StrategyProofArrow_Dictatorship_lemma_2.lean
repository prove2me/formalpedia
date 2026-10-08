-- Prove2me | Theorems.Thm_StrategyProofArrow_Dictatorship_lemma_2
-- name    : StrategyProofArrow.Dictatorship.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:48:16.465285+00:00
-- url     : https://prove2.me/theorems/e9c42526-0532-4ad9-85d5-6f47c6b357b5
-- title:
--   Lemma 2 — one voter, three alternatives: strategy-proof implies fully dictatorial or strong alternative-excluding
-- statement:
--   Consider a strict committee with a single individual and three alternatives, $\langle I_1,S_3,v^{1,3},T=T_p\rangle$ with $1\le p\le 3$. If $v^{1,3}$ is strategy-proof, then
--
--   $$v^{1,3}\ \text{is fully dictatorial}\quad\text{or}\quad v^{1,3}\ \text{is strong alternative-excluding.}$$
--
--   This is the base case of the paper's induction on the number of individuals for three alternatives.
--
--   **Formalization Note** One individual is `Fintype.card ι = 1`, three alternatives `Fintype.card A = 3`. The hypothesis $p\ge 1$ is kept as printed; $p\le 3$ holds automatically and is not stated.
-- source:
--   Satterthwaite, Strategy-proofness and Arrow's Conditions, Northwestern Discussion Paper No. 122 (rev. Dec. 12, 1974), Lemma 2, p. 15

import Mathlib
import Definitions.Def_StrategyProofArrow_Dictatorship_Basic

namespace StrategyProofArrow.Dictatorship

open AGT

/-- **Lemma 2** (Satterthwaite, p. 15). For a strict committee with one individual and three
alternatives, and `1 ≤ p ≤ 3`, a strategy-proof strict voting procedure is either fully
dictatorial or strong alternative-excluding. -/
theorem lemma_2 {ι A : Type*} [Fintype ι] [Fintype A] [DecidableEq ι]
    (hn : Fintype.card ι = 1) (hm : Fintype.card A = 3)
    (f : (ι → A → A → Prop) → A) (hp : 1 ≤ (range f).ncard)
    (hsp : IncentiveCompatible f) :
    FullyDictatorial f ∨ StrongAltExcluding f := by sorry

end StrategyProofArrow.Dictatorship
