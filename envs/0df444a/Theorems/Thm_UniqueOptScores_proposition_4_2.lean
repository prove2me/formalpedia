-- Prove2me | Theorems.Thm_UniqueOptScores_proposition_4_2
-- name    : UniqueOptScores.proposition_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:29:23.084211+00:00
-- url     : https://prove2.me/theorems/7461694a-1219-4dae-a581-1693980f9aa4
-- title:
--   Proposition 4.2 — $\mathrm{US}^A = \mathrm{UO}[1]^A \subseteq \mathrm{UO}[2]^A \subseteq \cdots \subseteq \mathrm{UO}^A_{\mathrm P} \subseteq D^A \subseteq \Theta^{\mathrm P,A}_2$
-- statement:
--   For every oracle $A$,
--   $$
--   \mathrm{US}^A = \mathrm{UO}[1]^A \subseteq \mathrm{UO}[2]^A \subseteq \cdots \qquad\text{and}\qquad \bigcup_{k \ge 1} \mathrm{UO}[k]^A \subseteq \mathrm{UO}^A_{\mathrm P} \subseteq D^A \subseteq \Theta^{\mathrm P,A}_2 .
--   $$
--   That is: exact-one acceptance is the first score level; $\mathrm{UO}[k]^A \subseteq \mathrm{UO}[k+1]^A$ for every $k \ge 1$; every fixed level lies in the polynomial-score class; and unique optimality with polynomially bounded scores lies within disjunctive access to $\mathrm{US}^A$, hence within parallel access to $\mathrm{NP}^A$.
--
--   This chain is the non-strict skeleton that the oracle constructions make strict.
--
--   Differences from the source:
--   - encoding: languages over {0,1}, oracle machines with polynomial running time valid for every oracle → Set (List Bool); HMBinPacking.OracleMachine with the set oracle [q ∈ A] and a polynomial clock quantified over all oracles A (IsClocked); reason: Lean convention for the paper's model (p.15, p.16); same instances
--   - encoding: nondeterministic polynomial-time oracle machines and their accepting computations (NP^A, US^A) → clocked deterministic verifiers over witnesses of length exactly p(|x|) (HMBinPacking.OracleMachine, pairing ⟨x, y⟩, acceptance = output 1); reason: paths are zero-padded choice strings of a common length (p.13), so accepting computations are in bijection with accepted witnesses; same classes
--   - encoding: candidate length p(n) ≥ 1, oracle-independent, polynomial-time computable and polynomially bounded → a polynomial p with p(n) ≥ 1 for all n; reason: padding to a polynomial bound with score 0 on nonzero padding preserves positive-score multiplicities and keeps an all-zero function rejecting; same classes
--   - encoding: scores written by the evaluator; timeout, malformed output or out-of-range score replaced by 0 → binary reading of the output word (every word is a number), values above the ceiling replaced by 0; clocked evaluators never time out; reason: same score functions
--   - encoding: transducer output list (y1, …, ym) → bit-doubled entries with separator 01, malformed output decoded as the empty list; reason: the paper's convention "Malformed lists become empty lists" (p.27); same class
--   - encoding: Θ^{P,A}_2 = P^{NP^A}_∥: polynomial-time computation with direct access to A and polynomially many nonadaptive queries to a fixed NP^A language → a clocked query generator T and a clocked decision machine E, both with oracle A, E accepting ⟨x, answer vector⟩ for the list output by T; reason: truth-table form of nonadaptive access (all NP^A queries prepared before any answer, p.14); E may recompute T; same class
-- source:
--   Ono, Seto, Unique Optimality with Polynomially Bounded Scores (manuscript, sha256 467bcf54…), Proposition 4.2, p.17

import Mathlib
import Definitions.Def_UniqueOptScores_US
import Definitions.Def_UniqueOptScores_UO
import Definitions.Def_UniqueOptScores_UOP
import Definitions.Def_UniqueOptScores_Dtt
import Definitions.Def_UniqueOptScores_Theta2

namespace UniqueOptScores

/-- **Proposition 4.2 (the inclusion chain).**
Ono, Seto, *Unique Optimality with Polynomially Bounded Scores* (manuscript, sha256 467bcf54…), Proposition 4.2, p.17: "For every oracle A, we have US^A = UO[1]^A ⊆ UO[2]^A ⊆ · · · and
⋃_{k≥1} UO[k]^A ⊆ UO^A_P ⊆ D^A ⊆ Θ^{P,A}_2." -/
theorem proposition_4_2 (A : Set (List Bool)) :
    US A = UO A 1 ∧ (∀ k : ℕ, 1 ≤ k → UO A k ⊆ UO A (k + 1)) ∧
      (⋃ k : ℕ, ⋃ (_ : 1 ≤ k), UO A k) ⊆ UOP A ∧ UOP A ⊆ Dtt A ∧ Dtt A ⊆ Theta2 A := by sorry

end UniqueOptScores
