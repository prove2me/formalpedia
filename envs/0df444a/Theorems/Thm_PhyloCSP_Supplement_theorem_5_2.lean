-- Prove2me | Theorems.Thm_PhyloCSP_Supplement_theorem_5_2
-- name    : PhyloCSP.Supplement.theorem_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T12:26:30.994775+00:00
-- url     : https://prove2.me/theorems/c57f404a-5e34-44e8-9476-2122f4d7f582
-- title:
--   Theorem 5.2 — tractability classification of phylogenetic CSPs (corrected: in the NP-completeness half, "neither (i) nor (ii)" is required of the satisfiable predicates)
-- statement:
--   This is the tractability classification of Bodirsky, Jonsson and Pham, in the setting of the paper (proved in Appendix A).
--
--   Let $\Pi$ be a constraint language.
--
--   1. If **(i)** every predicate in $\Pi$ can be expressed as a conjunction of split predicates applied to subsets of its variables, or **(ii)** every predicate in $\Pi$ is a caterpillar predicate, then $\mathrm{CSP}(\Pi)$ is **polynomially tractable**: one deterministic polynomial-time algorithm decides whether an instance is completely satisfiable and, if it is, outputs a tree satisfying all its constraints.
--   2. If neither (i) nor (ii) holds for the satisfiable predicates of $\Pi$ (those with $\mathrm{Sat}(\varphi)\neq\emptyset$; always-false predicates are ignored), then the decision problem
--   $$
--   \text{given an instance } I \text{ of } \mathrm{CSP}(\Pi),\ \text{is } I \text{ completely satisfiable?}
--   $$
--   is **NP-complete** (in NP, and NP-hard under polynomial-time many-one reductions).
--
--   The classification supplies the polynomially tractable relaxations of the paper's framework (Definition 5.3) and the NP-hardness half of Theorem 6.2.
--
--   **Formalization Note** Instances are read with the number of variables in unary (`encInstance`); polynomial tractability is `IsPolyTractable`; NP-completeness is the published `IntractableCoding.Weights.NPCompleteFor` (Turing-machine verifiers and reductions).
--
--   Differences from the source:
--   - correction: "Otherwise, CSP(Π) is NP-complete" (neither (i) nor (ii) for Π) → the NP-completeness half requires that neither (i) nor (ii) holds for the satisfiable predicates of Π (Sat(φ) ≠ ∅); when every predicate is satisfiable this is the printed hypothesis, and it covers every language with an always-false predicate for which the printed claim is true; reason: false unless P = NP as printed: for Π = {∅ of arity 1}, or Π = {all twelve caterpillars on four leaves, ∅ of arity 3}, neither (i) nor (ii) holds (the always-false predicate of arity 3 is the split predicate on two variables, but not a caterpillar predicate), yet an instance is satisfiable iff it has no always-false constraint, decidable in linear time; Appendix A uses "Each Rφ is nonempty" (p.44) and Section 2 assumes no always-false predicates (p.6)
--   - reading: polynomially tractable (p.2: an algorithm that distinguishes satisfiable from unsatisfiable instances and finds a satisfying solution) → one deterministic polynomial-time TM2 machine for the whole language outputs a satisfying tree (its triplet table) on every completely satisfiable instance and the empty word otherwise; reason: the paper fixes no machine model; this is its definition
--   - reading: NP-complete → the published NPCompleteFor (polynomially verifiable, and NP-hard under polynomial-time TM2 many-one reductions) for the decision problem "is the instance completely satisfiable"; reason: the meaning fixed on p.2
--   - encoding: instances and their size → code with the number of variables, predicate positions and variable indices in unary (encInstance); reason: n must not be binary (the output tree has n leaves); with n in unary the other unary numbers change lengths only polynomially
--   - encoding: variables x₁, …, xₙ; constraints with distinct arguments, repetitions allowed → Fin n (0-based); a List of predicate indices with embeddings Fin k ↪ Fin n; reason: Lean convention; same instances
-- source:
--   Makarychev, Approximation Algorithms for Satisfiable Phylogenetic CSPs, STOC 2027 submission (manuscript sha256 3444b6c029bce73ce9a6ad0ae6bc8386c291dcb0b1e504e8216c60cd4d682dac), Theorem 5.2, p.13 (PDF p.15); proof in Appendix A, pp.43–44 (PDF pp.45–46); polynomially tractable and NP-hard, p.2 (PDF p.4)

import Mathlib
import Definitions.Def_PhyloCSP_Supplement_Algorithms
import Definitions.Def_PhyloCSP_Supplement_Caterpillar
import Definitions.Def_IntractableCoding_Weights_NPComplete

set_option autoImplicit false

namespace PhyloCSP

namespace Supplement

/-- Makarychev, *Approximation Algorithms for Satisfiable Phylogenetic CSPs*, STOC 2027 submission
(manuscript sha256 3444b6c0…682dac), Theorem 5.2 (Bodirsky, Jonsson, and Pham), p.13 (PDF p.15);
proof in Appendix A, pp.43–44 (PDF pp.45–46): "Let Π be a constraint language. Then CSP(Π) is
polynomially tractable if either of the following holds: (i) Every predicate in Π can be expressed
as a conjunction of split predicates applied to subsets of its variables. (ii) Every predicate in
Π is a caterpillar predicate. Otherwise, CSP(Π) is NP-complete."

**Formalization Note.** Polynomially tractable is `IsPolyTractable` (one deterministic
polynomial-time machine for the whole language, p.2); NP-complete is the published
`IntractableCoding.Weights.NPCompleteFor` for the decision problem "is the instance completely
satisfiable", with instances in the code `encInstance`. **Correction:** in the NP-completeness
half, "neither (i) nor (ii) holds" is required of the satisfiable predicates of `Π` (those with
`Sat(φ) ≠ ∅`); always-false predicates are ignored. Without this the printed statement fails unless
P = NP: for `Π = {∅ of arity 1}`, or `Π` = {all twelve caterpillars on four leaves, ∅ of arity 3},
neither (i) nor (ii) holds, yet an instance is satisfiable iff it has no constraint on an
always-false predicate, which is decidable in linear time. When every predicate is satisfiable the
hypothesis is exactly "neither (i) nor (ii)", and it also covers every language with an
always-false predicate for which the printed claim is true (e.g. an NP-hard `φ` together with `∅`).
The proof in Appendix A uses "Each Rφ is nonempty" (p.44), and Section 2 (p.6) assumes "Π contains
neither always-true nor always-false predicates". -/
theorem theorem_5_2 (L : ConstraintLanguage) :
    (((∀ i, IsSplitConjunction (L.sat i)) ∨ (∀ i, IsCaterpillarPredicate (L.sat i))) →
      IsPolyTractable L) ∧
    (¬ ((∀ i, (L.sat i).Nonempty → IsSplitConjunction (L.sat i)) ∨
          (∀ i, (L.sat i).Nonempty → IsCaterpillarPredicate (L.sat i))) →
      IntractableCoding.Weights.NPCompleteFor (encInstance (L := L))
        (fun I : Instance L => CompletelySatisfiable I)) := by sorry

end Supplement

end PhyloCSP
