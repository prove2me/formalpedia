-- Prove2me | Theorems.Thm_UniqueOptScores_lemma_8_1
-- name    : UniqueOptScores.lemma_8_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:30:42.300136+00:00
-- url     : https://prove2.me/theorems/64767281-81f8-469b-81dd-399c109a23e8
-- title:
--   Lemma 8.1 — a uniformly c.e. comeager set of hierarchy oracles
-- statement:
--   Oracles are points of **oracle Cantor space** $\{0,1\}^{\{0,1\}^*}$ with the product topology, whose basic open sets fix finitely many answers. There is a uniformly computably enumerable family $(V_i)_{i\in\mathbb N}$ of dense open sets such that, with $G = \bigcap_i V_i$:
--
--   1. every oracle in $G$ satisfies the entire strict hierarchy of Lemma 7.1, with witnesses for the upper two gaps in $\mathrm{OR}_2(\mathrm{US}^A)$ and $\mathrm{NP}^A$;
--   2. $G$ is a dense comeager $G_\delta$ set and contains every weakly 1-generic oracle;
--   3. every nonempty finite-coordinate cylinder contains a recursive member of $G$, a member of $G$ of every Turing degree, and a nonempty perfect subset of $G$;
--   4. $G$ has measure zero for the fair-coin product measure.
--
--   Here the family is given by a c.e. relation $W \subseteq \mathbb N \times \{0,1\}^*$, $V_i$ being the union of the prefix cylinders (in length-lexicographic order) of the strings $\sigma$ with $(i,\sigma) \in W$.
--
--   **Formalization Note** A finite-coordinate cylinder is given by a finite set $s$ of strings and prescribed answers; such a cylinder is never empty. "A member of every Turing degree" is: for every oracle $B$ a member of $G$ in the cylinder that is Turing equivalent to $B$ (Mathlib's `TuringEquivalent` on the characteristic functions read in length-lexicographic order). The fair-coin product measure is Mathlib's `Measure.infinitePi` of uniform measures on $\{0,1\}$, applied to $G$.
--
--   Differences from the source:
--   - encoding: languages over {0,1}, oracle machines with polynomial running time valid for every oracle → Set (List Bool); HMBinPacking.OracleMachine with the set oracle [q ∈ A] and a polynomial clock quantified over all oracles A (IsClocked); reason: Lean convention for the paper's model (p.15, p.16); same instances
--   - encoding: nondeterministic polynomial-time oracle machines and their accepting computations (NP^A, US^A) → clocked deterministic verifiers over witnesses of length exactly p(|x|) (HMBinPacking.OracleMachine, pairing ⟨x, y⟩, acceptance = output 1); reason: paths are zero-padded choice strings of a common length (p.13), so accepting computations are in bijection with accepted witnesses; same classes
--   - encoding: candidate length p(n) ≥ 1, oracle-independent, polynomial-time computable and polynomially bounded → a polynomial p with p(n) ≥ 1 for all n; reason: padding to a polynomial bound with score 0 on nonzero padding preserves positive-score multiplicities and keeps an all-zero function rejecting; same classes
--   - encoding: scores written by the evaluator; timeout, malformed output or out-of-range score replaced by 0 → binary reading of the output word (every word is a number), values above the ceiling replaced by 0; clocked evaluators never time out; reason: same score functions
--   - encoding: transducer output list (y1, …, ym) → bit-doubled entries with separator 01, malformed output decoded as the empty list; reason: the paper's convention "Malformed lists become empty lists" (p.27); same class
--   - encoding: Θ^{P,A}_2 = P^{NP^A}_∥: polynomial-time computation with direct access to A and polynomially many nonadaptive queries to a fixed NP^A language → a clocked query generator T and a clocked decision machine E, both with oracle A, E accepting ⟨x, answer vector⟩ for the list output by T; reason: truth-table form of nonadaptive access (all NP^A queries prepared before any answer, p.14); E may recompute T; same class
--   - encoding: "the middle upper gap has a witness in OR_2(US^A)", "the last gap has a witness in NP^A" → ∃ L ∈ OR2(US^A) with L ∈ D^A ∖ UO^A_P, and ∃ L ∈ NP^A with L ∈ Θ^{P,A}_2 ∖ D^A; reason: a witness of a gap is a language in the larger class and not in the smaller one
--   - encoding: recursive oracle → ComputablePred (fun w => w ∈ A) on List Bool; reason: decidable membership; Mathlib's notion of a recursive set
--   - encoding: uniformly computably enumerable family of dense open sets (V_i) in oracle Cantor space → a c.e. relation W ⊆ ℕ × List Bool (REPred) with V_i = ceOpen W i, the union of the prefix cylinders of the σ with W(i, σ), on List Bool → Bool with the product topology; reason: each finite-coordinate cylinder is effectively a finite union of prefix cylinders (p.30); same families
--   - encoding: every nonempty cylinder → every finite-coordinate cylinder {χ | χ w = b w for w ∈ s}, s finite; reason: these are exactly the nonempty basic cylinders
--   - encoding: a member of every Turing degree → for every oracle B, a member χ of G in the cylinder with TuringEquivalent (charFn χ) (charFn B); reason: a Turing degree is the degree of some oracle; charFn reads it in length-lexicographic order
--   - reading: a perfect subset of G → a nonempty perfect subset P ⊆ G inside the cylinder; reason: the paper builds a homeomorphic copy of Cantor space (App. C, p.36); the empty set is perfect in Mathlib, so nonemptiness is stated (the stronger reading)
--   - encoding: fair-product measure zero → Measure.infinitePi (fun _ => (PMF.uniformOfFintype Bool).toMeasure) G = 0; reason: Mathlib's product of fair coins; outer measure of G
-- source:
--   Ono, Seto, Unique Optimality with Polynomially Bounded Scores (manuscript, sha256 467bcf54…), Lemma 8.1, p.29 (proof pp.29–30; remaining assertions proved in Appendix C, pp.35–36)

import Mathlib
import Definitions.Def_UniqueOptScores_HierarchyPackage
import Definitions.Def_UniqueOptScores_oracleOf
import Definitions.Def_UniqueOptScores_ceOpen
import Definitions.Def_UniqueOptScores_WeaklyOneGeneric
import Definitions.Def_UniqueOptScores_charFn

namespace UniqueOptScores

/-- **Lemma 8.1 (the comeager set), with the assertions proved in Appendix C.**
Ono, Seto, *Unique Optimality with Polynomially Bounded Scores* (manuscript, sha256 467bcf54…), Lemma 8.1, p.29 (proof pp.29–30 and App. C, pp.35–36): "There is a uniformly computably
enumerable family of dense open sets (V_i) in oracle Cantor space such that every A in G = ⋂_i V_i
satisfies the entire strict hierarchy of Lemma 7.1, with witnesses for the upper two gaps in
OR_2(US^A) and NP^A, respectively. The set G is a dense comeager G_δ and contains every weakly
1-generic oracle. Every nonempty cylinder contains a recursive member of G, a member of every Turing
degree, and a perfect subset of G. This particular set G has fair-product measure zero."

There is a c.e. relation `W ⊆ ℕ × {0,1}*` such that, with `V_i = ceOpen W i` (the union of the
prefix cylinders of the strings `σ` with `W(i, σ)`) and `G = ⋂ᵢ V_i`:
1. every `V_i` is dense;
2. every oracle in `G` satisfies `HierarchyPackage`;
3. `G` is dense, comeager and `G_δ`, and contains every weakly 1-generic oracle;
4. every finite-coordinate cylinder `{χ | χ w = b w for w ∈ s}` contains a recursive member of `G`,
   for every oracle `B` a member of `G` Turing equivalent to `B`, and a nonempty perfect subset of
   `G`;
5. `G` has measure zero for the fair-coin product measure on `{0,1}^{{0,1}*}`.

**Formalization Note.** Oracle Cantor space is `List Bool → Bool` with the product topology (`Bool`
discrete); its basic open sets fix finitely many answers. A finite-coordinate cylinder is given by
a finite set `s` of strings and prescribed answers `b`; such cylinders are never empty. Turing
equivalence is Mathlib's `TuringEquivalent` on the characteristic functions read in
length-lexicographic order (`charFn`). The perfect subset is required to be nonempty (Mathlib's
`Perfect ∅` holds). The measure is `Measure.infinitePi` of fair coins, applied to `G` (outer
measure). -/
theorem lemma_8_1 :
    ∃ W : ℕ × List Bool → Prop, REPred W ∧
      (∀ i, Dense (ceOpen W i)) ∧
      (∀ χ ∈ ⋂ i, ceOpen W i, HierarchyPackage (oracleOf χ)) ∧
      Dense (⋂ i, ceOpen W i) ∧
      (⋂ i, ceOpen W i) ∈ residual (List Bool → Bool) ∧
      IsGδ (⋂ i, ceOpen W i) ∧
      (∀ χ, WeaklyOneGeneric χ → χ ∈ ⋂ i, ceOpen W i) ∧
      (∀ (s : Finset (List Bool)) (b : List Bool → Bool),
        (∃ χ ∈ ⋂ i, ceOpen W i, (∀ w ∈ s, χ w = b w) ∧ ComputablePred (fun w => χ w = true)) ∧
        (∀ B : List Bool → Bool, ∃ χ ∈ ⋂ i, ceOpen W i, (∀ w ∈ s, χ w = b w) ∧
          TuringEquivalent (charFn χ) (charFn B)) ∧
        (∃ P ⊆ ⋂ i, ceOpen W i, P.Nonempty ∧ Perfect P ∧ ∀ χ ∈ P, ∀ w ∈ s, χ w = b w)) ∧
      MeasureTheory.Measure.infinitePi (fun _ : List Bool => (PMF.uniformOfFintype Bool).toMeasure)
        (⋂ i, ceOpen W i) = 0 := by sorry

end UniqueOptScores
