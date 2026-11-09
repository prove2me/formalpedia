-- Prove2me | Theorems.Thm_PhyloCSP_proposition_7_7
-- name    : PhyloCSP.proposition_7_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:27:54.453442+00:00
-- url     : https://prove2.me/theorems/02ab8c3b-17f2-4a52-aa36-abaad450afbd
-- title:
--   Proposition 7.7 — transformations of $\mathcal F$ induce tree transformations; invariant ones induce consistent ones
-- statement:
--   Every transformation $D$ of $\mathcal F$ induces a tree transformation $F$ such that
--   $$
--   p(\Pi,F)\ \ge\ p(\Pi,D)\qquad\text{for every constraint language }\Pi ;
--   $$
--   further, if the distribution of $D$ is invariant under $\mathrm{Aut}(\mathcal F)$, then this same $F$ is consistent.
--
--   Applied to the symmetrized relation $\hat D$, this gives the consistent transformation $\hat F$ of Theorem 3.2(i).
--
--   Differences from the source:
--   - generalization: constraint languages without always-true or always-false predicates (Section 2 convention) → every finite nonempty family of predicates of any arities; reason: Definition 1.2 permits such predicates and Section 2 only assumes their absence without loss of generality; the statement for all languages specializes to the restricted ones
--   - encoding: predicates as Boolean formulas in triplet atoms → their satisfying sets Sat(φ) on the variables Fin k; reason: p.1: every predicate is determined by Sat(φ) and every set of patterns is a predicate
--   - encoding: probabilities and guarantees in [0,1], with p(Π,F) − δ a real number → values in ℝ≥0∞ with truncated subtraction and the empty infimum ⊤; reason: same values whenever the infimum is over a nonempty set; when p(Π,F) − δ < 0 both inequalities are trivially true
--   - encoding: a probability distribution on ternary relations D on Z with every realization a binary tree structure → a probability measure on Z → Z → Z → Bool (product σ-algebra) giving full measure to tree relations; reason: a law on the closed set H of tree relations is the same as a law on all relations concentrated on H
--   - encoding: finite rooted binary trees up to label-preserving isomorphism, arbitrary leaf labels → patterns as rooted-triplet relations satisfying the axioms of Section 7.1 on finite leaf sets S ⊆ ℕ (S = ∅ included, with its single pattern); reason: the paper's own characterization (pp.1, 18); relabeling equivariance makes labels in ℕ cover every tree; the empty leaf set adds no constraint
--   - encoding: a constraint language (a finite nonempty set of predicates) → a finite nonempty indexed family (ConstraintLanguage) of predicates; reason: repetitions change no minimum over the language; every finite nonempty set is such a family
--   - encoding: the Fraïssé limit F = (Z, C) and its automorphism group Aut(F) → the concrete structure (Z, fraisseRel) of Definition 7.5, Z = Finset ℚ, and AutF its automorphism group; reason: Theorem 7.4 and Appendix B.1 identify the concrete structure with F, which is unique up to isomorphism; the statement is invariant under isomorphism
-- source:
--   Makarychev, Approximation Algorithms for Satisfiable Phylogenetic CSPs, STOC 2027 submission (manuscript sha256 3444b6c029bce73ce9a6ad0ae6bc8386c291dcb0b1e504e8216c60cd4d682dac), Proposition 7.7, p.21 (PDF p.23)

import Mathlib
import Definitions.Def_PhyloCSP_Consistent
import Definitions.Def_PhyloCSP_pPred
import Definitions.Def_PhyloCSP_TransformationOfF

set_option autoImplicit false

open MeasureTheory

namespace PhyloCSP

/-- Makarychev, *Approximation Algorithms for Satisfiable Phylogenetic CSPs*, STOC 2027
submission (manuscript sha256 3444b6c0…682dac), Proposition 7.7, p.21 (PDF p.23): "Every
transformation D of F induces a tree transformation F such that p(Π, F) ≥ p(Π, D) for every
constraint language Π. Further, if the distribution of D is invariant under Aut(F), then F is
consistent."

**Formalization Note.** The same tree transformation `F` satisfies both clauses: the guarantee
bound for every constraint language, and consistency whenever the law `μ` of `D` is
`Aut(F)`-invariant. -/
theorem proposition_7_7 (μ : Measure (Z → Z → Z → Bool)) (hμ : IsTransformationOfF μ) :
    ∃ F : TreeTransformation, (∀ L : ConstraintLanguage, pLangF μ L ≤ pLang F L) ∧
      (IsAutInvariant μ → Consistent F) := by sorry

end PhyloCSP
