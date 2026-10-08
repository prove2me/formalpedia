-- Prove2me | Theorems.Thm_StrategyProofArrow_WeakArrow_theorem_3_prime
-- name    : StrategyProofArrow.WeakArrow.theorem_3_prime
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:48:44.711027+00:00
-- url     : https://prove2.me/theorems/c38313c3-de6a-4e9d-ae45-a23361b9116d
-- title:
--   Theorem 3' (Arrow) — with indifference allowed, a social welfare function satisfying CS, NNR and IIA is dictatorial
-- statement:
--   Let a committee have $n\ge 2$ members and $m\ge 3$ alternatives, and let ballots and social orderings be weak orders, so indifference is allowed. Let $u$ be a social welfare function, assigning a weak social ordering $A=u(B)$ to every ballot set $B\in\pi_m^n$. If $u$ satisfies citizens' sovereignty, non-negative response and independence of irrelevant alternatives, then $u$ is dictatorial: some individual $i$ exists such that
--
--   $$x\,\bar B_i\,y \;\Longrightarrow\; x\,\bar A\,y\qquad\text{for all } B\in\pi_m^n \text{ and all } x,y\in S_m .$$
--
--   This is Arrow's general possibility theorem in its original setting of weak orders. The converse fails: a dictator's indifferences may be resolved by a rule that violates IIA.
--
--   **Formalization Note** "Dictatorial" is the negation of the paper's ND (p. 29) and says nothing about pairs the dictator is indifferent between. CS is stated for distinct alternatives; the printed "for every $x,y$" cannot hold at $x=y$ and would make the theorem vacuous. Weak orders are a structure (complete and transitive relation), and $u$ is defined on all of $\pi_m^n$. $n\ge 2$ and $m\ge 3$ are the printed hypotheses.
-- source:
--   Satterthwaite, Strategy-proofness and Arrow's Conditions, Northwestern Discussion Paper No. 122 (rev. Dec. 12, 1974), Theorem 3', p. 49

import Mathlib
import Definitions.Def_StrategyProofArrow_WeakArrow_Basic

namespace StrategyProofArrow.WeakArrow

/-- **Theorem 3' (Arrow)**, Satterthwaite p. 49: for a committee with `n ≥ 2` and `m ≥ 3`, whose
ballots are weak orders, a social welfare function satisfying CS, NNR and IIA is dictatorial: some
individual `i` exists such that, at every ballot set `B`, `x B̄_i y` implies `x Ā y`. -/
theorem theorem_3_prime {ι A : Type*} [Fintype ι] [Fintype A] [DecidableEq ι] [DecidableEq A]
    (hn : 2 ≤ Fintype.card ι) (hm : 3 ≤ Fintype.card A)
    (u : WeakProfile ι A → WeakOrder A)
    (hCS : CS u) (hNNR : NNR u) (hIIA : IIA u) :
    Dictatorial u := by sorry

end StrategyProofArrow.WeakArrow
