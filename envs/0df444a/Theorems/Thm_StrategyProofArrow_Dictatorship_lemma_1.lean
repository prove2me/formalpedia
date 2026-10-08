-- Prove2me | Theorems.Thm_StrategyProofArrow_Dictatorship_lemma_1
-- name    : StrategyProofArrow.Dictatorship.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:48:04.880325+00:00
-- url     : https://prove2.me/theorems/bedaa81e-07cd-4017-bddd-6022cace7a8f
-- title:
--   Lemma 1 — a strategy-proof strict voting procedure satisfies Condition U
-- statement:
--   Consider a strict committee with $n\ge 1$ individuals and $m\ge 3$ alternatives, and a strict voting procedure $v^{nm}$ whose range $T=T_p$ has $p\ge 1$ elements. If $v^{nm}$ is strategy-proof, then it satisfies Condition U: for every strict ballot set $B\in\rho^n_m$ and every $x\in T$,
--
--   $$\Psi_T(B_1)=\dots=\Psi_T(B_n)=\{x\}\ \Longrightarrow\ v^{nm}(B)=x .$$
--
--   In words, if every individual ranks $x$ above every other element of the range, the procedure selects $x$. Condition U is the Pareto-type property on which the definition of strong alternative-excluding procedures, and the rest of the proof of Theorem 1, rest.
--
--   **Formalization Note** Strategy-proofness is `AGT.IncentiveCompatible`. $n$, $m$, $p$ are `Fintype.card ι`, `Fintype.card A` and `(range f).ncard`. The paper states $m\ge 3$ and $p\ge 1$ as hypotheses; both are kept, although the conclusion does not need them.
-- source:
--   Satterthwaite, Strategy-proofness and Arrow's Conditions, Northwestern Discussion Paper No. 122 (rev. Dec. 12, 1974), Lemma 1, p. 13

import Mathlib
import Definitions.Def_StrategyProofArrow_Dictatorship_Basic

namespace StrategyProofArrow.Dictatorship

open AGT

/-- **Lemma 1** (Satterthwaite, p. 13). For a strict committee with `n ≥ 1`, `m ≥ 3` and
`p ≥ 1`, every strategy-proof strict voting procedure satisfies Condition U. -/
theorem lemma_1 {ι A : Type*} [Fintype ι] [Fintype A] [DecidableEq ι]
    (hn : 1 ≤ Fintype.card ι) (hm : 3 ≤ Fintype.card A)
    (f : (ι → A → A → Prop) → A) (hp : 1 ≤ (range f).ncard)
    (hsp : IncentiveCompatible f) :
    ConditionU f := by sorry

end StrategyProofArrow.Dictatorship
