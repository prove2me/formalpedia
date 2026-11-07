-- Prove2me | Theorems.Thm_UniqueOptScores_theorem_1_2_simultaneous_hierarchy
-- name    : UniqueOptScores.theorem_1_2_simultaneous_hierarchy
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:31:45.977773+00:00
-- url     : https://prove2.me/theorems/204d47fa-add3-4eb3-82e7-6db2318a4a13
-- title:
--   Theorem 1.2 — simultaneous hierarchy relative to a recursive oracle and to comeager many oracles
-- statement:
--   **(a)** There is a recursive oracle $A$ such that
--   $$
--   \mathrm{US}^A = \mathrm{UO}[1]^A \subsetneq \mathrm{UO}[2]^A \subsetneq \mathrm{UO}[3]^A \subsetneq \cdots ,\qquad \bigcup_{k\ge1}\mathrm{UO}[k]^A \subsetneq \mathrm{UO}^A_{\mathrm P} \subsetneq D^A \subsetneq \Theta^{\mathrm P,A}_2 ,
--   $$
--   the gap above $\mathrm{UO}^A_{\mathrm P}$ having a witness in $\mathrm{OR}_2(\mathrm{US}^A)$ and the gap above $D^A$ a witness in $\mathrm{NP}^A$.
--
--   **(b)** A comeager set of oracles satisfies this entire package, and it contains every weakly 1-generic oracle.
--
--   Here $\mathrm{UO}[k]^A$ recognizes a unique maximizer of a polynomial-time score function with values in $\{0,\dots,k\}$ over all candidate strings of a polynomial length, $\mathrm{UO}^A_{\mathrm P}$ allows a polynomial numerical score bound, $D^A = \mathrm P_{\mathrm{dtt}}(\mathrm{US}^A)$ and $\Theta^{\mathrm P,A}_2 = \mathrm P^{\mathrm{NP}^A}_\parallel$; all machines carry polynomial clocks valid for every oracle. A set of oracles is comeager if it contains a countable intersection of dense open sets of oracle Cantor space, whose basic open sets fix finitely many oracle answers.
--
--   **Formalization Note** Oracles of part (b) are points of `List Bool → Bool` (product topology), read as languages by `oracleOf`; comeager is membership in Mathlib's `residual`.
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
--   - encoding: a comeager set of oracles → G ∈ residual (List Bool → Bool), oracles read by oracleOf; reason: Mathlib's comeager filter on oracle Cantor space with the product topology, whose basic open sets fix finitely many answers (p.3)
--   - encoding: weakly 1-generic oracle (meets every c.e. dense open set) → WeaklyOneGeneric: meets every REPred dense set of finite strings along the length-lexicographic order; reason: standard definition with the paper's identification (p.30)
-- source:
--   Ono, Seto, Unique Optimality with Polynomially Bounded Scores (manuscript, sha256 467bcf54…), Theorem 1.2, p.3 (proved in Lemmas 7.1 and 8.1; proof of Theorem 1.2, p.30)

import Mathlib
import Definitions.Def_UniqueOptScores_SimultaneousHierarchy
import Definitions.Def_UniqueOptScores_oracleOf
import Definitions.Def_UniqueOptScores_WeaklyOneGeneric

namespace UniqueOptScores

/-- **Theorem 1.2 (simultaneous hierarchy).**
Ono, Seto, *Unique Optimality with Polynomially Bounded Scores* (manuscript, sha256 467bcf54…), Theorem 1.2, p.3: "There is a recursive oracle A such that US^A = UO[1]^A ⊊ UO[2]^A ⊊
UO[3]^A ⊊ · · · , and ⋃_{k≥1} UO[k]^A ⊊ UO^A_P ⊊ D^A ⊊ Θ^{P,A}_2. The gap above UO^A_P has a
witness in OR_2(US^A), and the gap above D^A has a witness in NP^A. A comeager set of oracles
satisfies this entire package, and it contains every weakly 1-generic oracle."

(a) Some recursive oracle `A` satisfies `SimultaneousHierarchy A`; (b) there is a comeager set `G`
of oracles, each satisfying `SimultaneousHierarchy`, that contains every weakly 1-generic oracle.

**Formalization Note.** "Recursive" is `ComputablePred`; oracles of part (b) are points
`χ : List Bool → Bool` of oracle Cantor space (product topology, basic open sets fixing finitely
many answers), read as languages by `oracleOf`; comeager is membership in Mathlib's `residual`. -/
theorem theorem_1_2_simultaneous_hierarchy :
    (∃ A : Set (List Bool), ComputablePred (fun w => w ∈ A) ∧ SimultaneousHierarchy A) ∧
    ∃ G : Set (List Bool → Bool), G ∈ residual (List Bool → Bool) ∧
      (∀ χ ∈ G, SimultaneousHierarchy (oracleOf χ)) ∧
      ∀ χ, WeaklyOneGeneric χ → χ ∈ G := by sorry

end UniqueOptScores
