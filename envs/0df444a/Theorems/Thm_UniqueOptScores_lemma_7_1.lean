-- Prove2me | Theorems.Thm_UniqueOptScores_lemma_7_1
-- name    : UniqueOptScores.lemma_7_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:31:14.9122+00:00
-- url     : https://prove2.me/theorems/71a3f1fa-007a-4499-b62e-6a6725111ee9
-- title:
--   Lemma 7.1 — one recursive oracle for the whole strict hierarchy
-- statement:
--   There is a recursive oracle $A \subseteq \{0,1\}^*$ for which every fixed-level inclusion $\mathrm{UO}[k]^A \subseteq \mathrm{UO}[k+1]^A$ ($k \ge 1$) is strict and
--   $$
--   \bigcup_{k\ge1} \mathrm{UO}[k]^A \subsetneq \mathrm{UO}^A_{\mathrm P} \subsetneq D^A \subsetneq \Theta^{\mathrm P,A}_2 ,
--   $$
--   the gap above $\mathrm{UO}^A_{\mathrm P}$ having a witness in $\mathrm{OR}_2(\mathrm{US}^A)$ and the gap above $D^A$ a witness in $\mathrm{NP}^A$.
--
--   This is the first half of Theorem 1.2 (with $\mathrm{US}^A = \mathrm{UO}[1]^A$ from Proposition 4.2).
--
--   Differences from the source:
--   - encoding: recursive oracle → ComputablePred (fun w => w ∈ A) on List Bool; reason: decidable membership; Mathlib's notion of a recursive set
--   - encoding: languages over {0,1}, oracle machines with polynomial running time valid for every oracle → Set (List Bool); HMBinPacking.OracleMachine with the set oracle [q ∈ A] and a polynomial clock quantified over all oracles A (IsClocked); reason: Lean convention for the paper's model (p.15, p.16); same instances
--   - encoding: nondeterministic polynomial-time oracle machines and their accepting computations (NP^A, US^A) → clocked deterministic verifiers over witnesses of length exactly p(|x|) (HMBinPacking.OracleMachine, pairing ⟨x, y⟩, acceptance = output 1); reason: paths are zero-padded choice strings of a common length (p.13), so accepting computations are in bijection with accepted witnesses; same classes
--   - encoding: candidate length p(n) ≥ 1, oracle-independent, polynomial-time computable and polynomially bounded → a polynomial p with p(n) ≥ 1 for all n; reason: padding to a polynomial bound with score 0 on nonzero padding preserves positive-score multiplicities and keeps an all-zero function rejecting; same classes
--   - encoding: scores written by the evaluator; timeout, malformed output or out-of-range score replaced by 0 → binary reading of the output word (every word is a number), values above the ceiling replaced by 0; clocked evaluators never time out; reason: same score functions
--   - encoding: transducer output list (y1, …, ym) → bit-doubled entries with separator 01, malformed output decoded as the empty list; reason: the paper's convention "Malformed lists become empty lists" (p.27); same class
--   - encoding: Θ^{P,A}_2 = P^{NP^A}_∥: polynomial-time computation with direct access to A and polynomially many nonadaptive queries to a fixed NP^A language → a clocked query generator T and a clocked decision machine E, both with oracle A, E accepting ⟨x, answer vector⟩ for the list output by T; reason: truth-table form of nonadaptive access (all NP^A queries prepared before any answer, p.14); E may recompute T; same class
--   - encoding: "the middle upper gap has a witness in OR_2(US^A)", "the last gap has a witness in NP^A" → ∃ L ∈ OR2(US^A) with L ∈ D^A ∖ UO^A_P, and ∃ L ∈ NP^A with L ∈ Θ^{P,A}_2 ∖ D^A; reason: a witness of a gap is a language in the larger class and not in the smaller one
-- source:
--   Ono, Seto, Unique Optimality with Polynomially Bounded Scores (manuscript, sha256 467bcf54…), Lemma 7.1, p.26

import Mathlib
import Definitions.Def_UniqueOptScores_HierarchyPackage

namespace UniqueOptScores

/-- **Lemma 7.1 (one recursive oracle).**
Ono, Seto, *Unique Optimality with Polynomially Bounded Scores* (manuscript, sha256 467bcf54…), Lemma 7.1, p.26: "There is one recursive oracle A for which every fixed-level inclusion
UO[k]^A ⊆ UO[k + 1]^A is strict, and ⋃_{k≥1} UO[k]^A ⊊ UO^A_P ⊊ D^A ⊊ Θ^{P,A}_2 . The middle upper
gap has a witness in OR_2(US^A), and the last gap has a witness in NP^A."

**Formalization Note.** "Recursive" is decidable membership (`ComputablePred`). -/
theorem lemma_7_1 :
    ∃ A : Set (List Bool), ComputablePred (fun w => w ∈ A) ∧ HierarchyPackage A := by sorry

end UniqueOptScores
