-- Prove2me | Theorems.Thm_StrategyProofArrow_WeakArrow_theorem_3
-- name    : StrategyProofArrow.WeakArrow.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:48:30.926267+00:00
-- url     : https://prove2.me/theorems/337ee852-c441-4cb9-b34d-02b17906587a
-- title:
--   Theorem 3 (Arrow) — a strict social welfare function satisfies CS, NNR and IIA iff it is dictatorial
-- statement:
--   Let a committee have $n\ge 2$ members and $m\ge 3$ alternatives, and let every ballot be a strong order (no indifference). Let $\mu$ be a strict social welfare function, assigning a strong social ordering $\mu(C)$ to every strong ballot set $C\in\rho_m^n$. Then
--
--   $$\mu \text{ satisfies CS, NNR and IIA} \iff \exists\, i \;\forall C\in\rho_m^n\;\forall x,y:\; x\,\bar C_i\,y \Rightarrow x\,\overline{\mu(C)}\,y .$$
--
--   This is Arrow's general possibility theorem for strict ballots and strict social orderings, with Arrow's original conditions of citizens' sovereignty and non-negative response in place of the Pareto condition. Satterthwaite derives it from the Gibbard–Satterthwaite theorem through the correspondence between strategy-proof voting procedures and Arrovian social welfare functions.
--
--   **Formalization Note** Strong ballot sets and strong social orderings are subtypes, so $\mu$ is defined on admissible profiles only. CS is stated for distinct alternatives $x\neq y$ (the printed "for every $x,y$" cannot hold at $x=y$). "Dictatorial" is the negation of the paper's non-dictatorship condition ND (p. 29). $n\ge 2$ and $m\ge 3$ are the printed hypotheses.
-- source:
--   Satterthwaite, Strategy-proofness and Arrow's Conditions, Northwestern Discussion Paper No. 122 (rev. Dec. 12, 1974), Theorem 3, p. 36

import Mathlib
import Definitions.Def_StrategyProofArrow_WeakArrow_Basic

namespace StrategyProofArrow.WeakArrow

/-- **Theorem 3 (Arrow)**, Satterthwaite p. 36: for a strict committee with `n ≥ 2` and `m ≥ 3`,
a strict social welfare function satisfies CS, NNR and IIA if and only if it is dictatorial. -/
theorem theorem_3 {ι A : Type*} [Fintype ι] [Fintype A] [DecidableEq ι] [DecidableEq A]
    (hn : 2 ≤ Fintype.card ι) (hm : 3 ≤ Fintype.card A)
    (μ : StrongProfile ι A → StrongOrder A) :
    (StrictCS μ ∧ StrictNNR μ ∧ StrictIIA μ) ↔ StrictDictatorial μ := by sorry

end StrategyProofArrow.WeakArrow
