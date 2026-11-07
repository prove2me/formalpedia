-- Prove2me | Theorems.Thm_QBFBackdoor_dual_holds_iff
-- name    : QBFBackdoor.dual_holds_iff
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:34:08.587564+00:00
-- url     : https://prove2.me/theorems/0cc9453a-ceb5-4fbe-98e6-8ac06b241854
-- title:
--   Proof of Lemma 5.4 — $\Phi\Leftrightarrow\neg\bar\Phi$ (de Morgan)
-- statement:
--   Let $\Phi=Q.(C_1\wedge\cdots\wedge C_m)$ be a quantified CNF formula, and let $\bar\Phi=\bar Q.(\bar C_1\vee\cdots\vee\bar C_m)$ be its dual: $\bar Q$ swaps $\forall$ and $\exists$, and $\bar C_i$ is the conjunction of the negated literals of $C_i$. Then $\bar\Phi$ has $m$ disjuncts, each in $\Gamma_{\mathrm{AFF}}$, and
--
--   $$
--   \Phi \text{ is true} \iff \bar\Phi \text{ is false}.
--   $$
--
--   This turns the falsity of quantified 3-CNF into the truth of a disjunctive QBF over $\Gamma_{\mathrm{AFF}}$, which gives the hardness half of Lemma 5.4.
--
--   Differences from the source:
--   - generalization: Φ a quantified 3-CNF formula → Φ a CNF QBF with clauses of any width; reason: the de Morgan argument does not use the width; the 3-CNF case is a special case
--   - encoding: C̄i = (¬x) ∧ (¬y) ∧ (z), atoms in the order of the literals → atoms of C̄i in the order of Finset.toList; reason: a conjunction does not depend on the order of its atoms
--   - encoding: variables x1, …, xn and prefix Q1x1 … Qnxn → variables Fin n quantified in index order, q j = true meaning ∃; reason: relabelling; same formulas
-- source:
--   Eriksson, Lagerkvist, Ordyniak, Osipov, Panolan, Rychlicki, Backdoors for Quantified Boolean Formulas, arXiv:2604.15927 (held version, sha256 3ea1662e…), proof of Lemma 5.4, p.23

import Mathlib
import Definitions.Def_QBFBackdoor_dual

namespace QBFBackdoor

open MDPComplexity.PartiallyObserved

/-- **De Morgan duality, `Φ ⇔ ¬Φ̄`.** Eriksson, Lagerkvist, Ordyniak, Osipov, Panolan, Rychlicki, *Backdoors for Quantified Boolean
Formulas*, arXiv:2604.15927 (held version, sha256 3ea1662e…), proof of Lemma 5.4, p.23: "By de Morgan's law,
Φ ⇔ ¬Φ̄, and Φ̄ is a disjunction of m formulas in ΓAFF."

For every CNF QBF `φ` with `m` clauses, `φ` is true iff its dual `Φ̄` (prefix flipped, each
clause replaced by the conjunction of the negations of its literals) is false, and `Φ̄` has `m`
disjuncts.

**Formalization Note** Stated for clauses of every width, not only 3-CNF; the 3-CNF case of the
proof is a special case. -/
theorem dual_holds_iff {n m : ℕ} (φ : QBF n m) :
    (dual φ).disj.length = m ∧ (φ.holds ↔ ¬ (dual φ).holds) := by sorry

end QBFBackdoor
